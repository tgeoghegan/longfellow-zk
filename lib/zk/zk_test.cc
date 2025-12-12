// Copyright 2025 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp_p128.h"
#include "algebra/reed_solomon.h"
#include "arrays/dense.h"
#include "circuits/compiler/circuit_dump.h"
#include "circuits/compiler/compiler.h"
#include "circuits/ecdsa/verify_circuit.h"
#include "circuits/ecdsa/verify_witness.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "ec/p256.h"
#include "proto/circuit.h"
#include "random/random.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_testing.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

// Test fixture for ZK.
// This class produces static versions of a test circuit that can be used for
// many tests.
class ZKTest : public testing::Test {
  using Nat = Fp256Base::N;
  using Elt = Fp256Base::Elt;
  using Verw = VerifyWitness3<P256, Fp256Scalar>;

 protected:
  ZKTest()
      : pkx_(p256_base.of_string("0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaa"
                                 "f686c8f9ff5e7c6368d9c")),
        pky_(p256_base.of_string("0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b"
                                 "2fe38e6f58626767f9e75")),
        omega_x_(p256_base.of_string("0xf90d338ebd84f5665cfc85c67990e3379fc9563"
                                     "b382a4a4c985a65324b242562")),
        omega_y_(p256_base.of_string("0xb9e81e42bc97cc4da04fc2e20106e34084738a6"
                                     "474d232c6dbf4174f60a43eac")),
        e_("0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7a"
           "e"),
        r_("0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671"),
        s_("0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410ff4f6dd4"
           "0") {
    set_log_level(INFO);
    w_ = std::make_unique<Dense<Fp256Base>>(1, circuit1_->ninputs);
    DenseFiller<Fp256Base> filler(*w_);

    Verw vw(p256_scalar, p256);
    vw.compute_witness(pkx_, pky_, e_, r_, s_);
    filler.push_back(p256_base.one());
    filler.push_back(pkx_);
    filler.push_back(pky_);
    filler.push_back(p256_base.to_montgomery(e_));
    vw.fill_witness(filler);

    // public input
    pub_ = std::make_unique<Dense<Fp256Base>>(1, circuit1_->ninputs);
    DenseFiller<Fp256Base> pubfill(*pub_);
    pubfill.push_back(p256_base.one());
    pubfill.push_back(pkx_);
    pubfill.push_back(pky_);
    pubfill.push_back(p256_base.to_montgomery(e_));
  }

  static void SetUpTestCase() {
    if (circuit1_ == nullptr) {
      using CompilerBackend = CompilerBackend<Fp256Base>;
      using LogicCircuit = Logic<Fp256Base, CompilerBackend>;
      using EltW = typename LogicCircuit::EltW;
      using Verc = VerifyCircuit<LogicCircuit, Fp256Base, P256>;
      QuadCircuit<Fp256Base> Q(p256_base);
      const CompilerBackend cbk(&Q);
      const LogicCircuit lc(&cbk, p256_base);

      Verc verc(lc, p256, n256_order);

      EltW pkx = lc.eltw_input(), pky = lc.eltw_input(), e = lc.eltw_input();
      Q.private_input();
      Verc::Witness vwc;
      vwc.input(lc);
      verc.verify_signature3(pkx, pky, e, vwc);
      circuit1_ = Q.mkcircuit(1).release();
    }
  }

  static void TearDownTestCase() {
    if (circuit1_ != nullptr) {
      delete circuit1_;
      circuit1_ = nullptr;
    }
  }

  static Circuit<Fp256Base>* circuit1_;
  std::unique_ptr<Dense<Fp256Base>> w_;
  std::unique_ptr<Dense<Fp256Base>> pub_;
  const Elt pkx_, pky_, omega_x_, omega_y_;
  const Nat e_, r_, s_;
};

Circuit<Fp256Base>* ZKTest::circuit1_ = nullptr;

TEST_F(ZKTest, prover_verifier) {
  run2_test_zk(*circuit1_, *w_, *pub_, p256_base, omega_x_, omega_y_,
               1ull << 31);
}

TEST_F(ZKTest, failing_test) {
  auto W_fail = Dense<Fp256Base>(1, circuit1_->ninputs);
  DenseFiller<Fp256Base> wf(W_fail);
  wf.push_back(p256_base.one());
  wf.push_back(pkx_);
  wf.push_back(pky_);
  wf.push_back(p256_base.to_montgomery(e_));
  run_failing_test_zk2(*circuit1_, W_fail, *pub_, p256_base, omega_x_, omega_y_,
                       1ull << 31);
}

TEST_F(ZKTest, short_proofs_fail) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  std::vector<uint8_t> buf(213348, 1u);
  // Check that short proofs fail.
  for (size_t i = 1; i < buf.size(); ++i) {
    ReadBuffer rb(buf.data(), buf.size() - i);
    EXPECT_FALSE(zkpv.read(rb, p256_base));
  }
}

TEST_F(ZKTest, random_proofs_fail) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  std::vector<uint8_t> buf(213348, 1u);
  for (size_t i = 0; i < buf.size(); ++i) {
    buf[i] = random() & 0xff;
  }
  ReadBuffer rb(buf);
  EXPECT_FALSE(zkpv.read(rb, p256_base));
}

TEST_F(ZKTest, elt_out_of_range) {
  ZkProof<Fp256Base> zkpv(*circuit1_, 4, 189);
  // Initialize the proof so that all of the elt are in range.
  std::vector<uint8_t> buf(213348, 0u);

  // Set the first two run lengths to be 1.
  buf[(3366 + 189) * 32] = 1;
  buf[(3366 + 189 + 1) * 32 + 4] = 1;

  // Selectively create bad elts at these indices and assert the parse fails.
  size_t bad_elts[] = {
      1 * 32,
      13 * 32, /* bad elts in sumcheck transcript */
      451 * 32,
      456 * 32, /* bad elts in com proof, block */
      1133 * 32,
      1134 * 32, /* bad elts in com proof, dblock */
      2496 * 32,
      2497 * 32, /* bad elts in com proof, r */
      2685 * 32,
      2686 * 32,                 /* bad elts in com proof, d-b */
      (3366 + 189) * 32 + 4,     /* bad elt in first run */
      (3366 + 189 + 1) * 32 + 8, /* bad elt in second run */
  };
  for (size_t bi = 0; bi < sizeof(bad_elts) / sizeof(size_t); ++bi) {
    for (size_t i = 0; i < 32; ++i) {
      buf[bad_elts[bi] + i] = 0xff;
    }
    ReadBuffer rb(buf);
    EXPECT_FALSE(zkpv.read(rb, p256_base));
    for (size_t i = 0; i < 32; ++i) {
      buf[bad_elts[bi] + i] = 0x00;
    }
  }
}

TEST(ZK, test_circuit_io) {
  auto c = Circuit<Fp256Base>{
      .nv = 2,
      .logv = 1,
      .nc = 1,
      .logc = 0,
      .nl = 1,
      .ninputs = 4,
      .npub_in = 4,
  };
  c.l.push_back(Layer<Fp256Base>{.nw = 7, .logw = 3, .quad = nullptr});
  ZkProof<Fp256Base> zkpv(c, 4, 16);
  std::vector<uint8_t> buf(213348, 0x02u);
  ReadBuffer rb(buf);
  EXPECT_FALSE(zkpv.read(rb, p256_base));
}

void dump(const char* msg, const std::vector<uint8_t> bytes) {
  size_t sz = bytes.size();

  for (size_t i = 0; i < sz; ++i) {
    printf("%02x", bytes[i]);
  }
}

// This mock random engine returns a fixed sequence of random bytes in order
// to create "simple" examples for the RFC.
class TestRandomEngine : public RandomEngine {
 public:
  TestRandomEngine() = default;
  void bytes(uint8_t* buf, size_t n) override {
    memset(buf, 0, n);
    buf[0] = 2;
  }
};

// This Test method generates the examples used in our RFC for a circuit,
// for a sumcheck run, and a Ligero run.
// First, it defines a small test circuit:
//     C(n, m, s) = 0 if and only if n is the m-th s-gonal number.
// i.e., verifies that 2n = (s-2)m^2 - (s - 4)*m
// For example, C(45, 5, 6) = 0.
// This relationship was chosen so that it has depth > 2 but not too many
// wires or terms.
TEST(ZK, Rfc_testvector1) {
  set_log_level(INFO);

  using Fp128 = Fp128<>;
  using CompilerBackend = CompilerBackend<Fp128>;
  using LogicCircuit = Logic<Fp128, CompilerBackend>;
  using EltW = LogicCircuit::EltW;
  const Fp128 Fg;
  std::unique_ptr<Circuit<Fp128>> circuit;

  /*scope to delimit compile-time*/ {
    QuadCircuit<Fp128> Q(Fg);
    CompilerBackend cbk(&Q);
    const LogicCircuit LC(&cbk, Fg);
    EltW n = LC.eltw_input();
    Q.private_input();
    EltW m = LC.eltw_input();
    EltW s = LC.eltw_input();
    EltW sm2 = LC.sub(&s, LC.konst(2));
    EltW m2 = LC.mul(&m, m);
    EltW sm2m2 = LC.mul(&sm2, m2);
    EltW sm4 = LC.sub(&s, LC.konst(4));
    EltW sm4m = LC.mul(&sm4, m);
    EltW t = LC.sub(&sm2m2, sm4m);
    EltW k2 = LC.konst(2);
    EltW nn = LC.mul(&n, k2);
    LC.assert_eq(&t, nn);
    circuit = Q.mkcircuit(1);
    dump_info("rfc_sgonal", 1, Q);
  }

  // Serialize the circuit.
  std::vector<uint8_t> bytes;
  CircuitRep<Fp128> cr(Fg, FP128_ID);
  cr.to_bytes(*circuit, bytes);
  printf("\"serialized_circuit\": \"");
  dump("circuit", bytes);
  printf("\",\n");

  // Sample input.
  auto W = Dense<Fp128>(1, circuit->ninputs);
  DenseFiller<Fp128> filler(W);

  filler.push_back(Fg.one());
  filler.push_back(Fg.of_scalar(45));
  filler.push_back(Fg.of_scalar(5));
  filler.push_back(Fg.of_scalar(6));

  Transcript transcript((uint8_t*)"test", 4);
  TestRandomEngine rng;

  using FftConvolutionFactory = FFTConvolutionFactory<Fp128>;
  auto omega = Fg.of_string("164956748514267535023998284330560247862");
  uint64_t omega_order = 1ull << 32;
  FftConvolutionFactory fft(Fg, omega, omega_order);
  using RSFactory = ReedSolomonFactory<Fp128, FftConvolutionFactory>;
  const RSFactory rsf(fft, Fg);

  ZkProof<Fp128> zk_proof(*circuit, 4, 6);
  ZkProver<Fp128, RSFactory> prover(*circuit, Fg, rsf);
  prover.commit(zk_proof, W, transcript, rng);
  EXPECT_TRUE(prover.prove(zk_proof, W, transcript));

  printf("done proving\n");

  std::vector<uint8_t> sumcheck_proof_bytes;
  zk_proof.write_sc_proof(zk_proof.proof, sumcheck_proof_bytes, Fg);
  printf("\"sumcheck_proof\": \"");
  dump("sumcheck_proof", sumcheck_proof_bytes);
  printf("\",\n");

  std::vector<uint8_t> commitment_bytes;
  zk_proof.write_com(zk_proof.com, commitment_bytes, Fg);
  printf("\"ligero_commitment\": \"");
  dump("ligero commitment", commitment_bytes);
  printf("\",\n");

  printf("\"constraints\": {\n");
  printf("    \"linear_rhs\": [\n");
    std::vector<uint8_t> buf(16, 0);
  for (size_t i = 0; i < prover.linear_constraint_rhs_.size(); i++) {
    Fg.to_bytes_field(&buf[0], prover.linear_constraint_rhs_[i]);
    printf("        \"");
    dump("", buf);
    printf("\"");
    if (i + 1 != prover.linear_constraint_rhs_.size()) {
        printf(",");
    }
    printf("\n");
  }
  printf("    ],\n"); // linear_rhs
  printf("    \"quadratic\": [\n");
  for (size_t i = 0; i < prover.lqc_.size(); i++) {
    printf("        { \"x\": %zu, \"y\": %zu, \"z\": %zu }", prover.lqc_[i].x, prover.lqc_[i].y,
           prover.lqc_[i].z);
    if (i + 1 != prover.lqc_.size()) {
      printf(",");
    }
    printf("\n");
  }
  printf("    ]\n"); // quadratic
  printf("}\n"); // constraints

  std::vector<uint8_t> ligero_bytes;
  zk_proof.write_com_proof(zk_proof.com_proof, ligero_bytes, Fg);
  printf("\"ligero_proof\": \"");
  dump("ligero_proof", ligero_bytes);
  printf("\",\n");
}

}  // namespace
}  // namespace proofs
