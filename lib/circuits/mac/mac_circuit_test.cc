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

#include "circuits/mac/mac_circuit.h"

#include <cerrno>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <cstdint>
#include <memory>
#include <unistd.h>
#include <utility>

#include "arrays/dense.h"
#include "circuits/compiler/circuit_dump.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/bit_plucker.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/mac/mac_reference.h"
#include "circuits/mac/mac_witness.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "proto/circuit.h"
#include "random/secure_random_engine.h"
#include "sumcheck/circuit.h"
#include "sumcheck/testing.h"
#include "util/log.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

void dump_hex_to_file(FILE* out, const std::vector<uint8_t> bytes) {
  size_t sz = bytes.size();

  for (size_t i = 0; i < sz; ++i) {
    fprintf(out, "%02x", bytes[i]);
  }
}

void dump_to_file(FILE *out, const std::vector<uint8_t> bytes) {
  fwrite(&bytes[0], bytes.size(), 1, out);
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

// This test subsumes the evaluation test.
TEST(MAC, full_circuit_test_128) {
  set_log_level(INFO);
  constexpr size_t kNum = 3;

  size_t ninput;
  std::unique_ptr<Circuit<Fp256Base>> circuit;

  /*scope to delimit compile-time*/ {
    using CompilerBackend = CompilerBackend<Fp256Base>;
    using LogicCircuit = Logic<Fp256Base, CompilerBackend>;
    using v128 = LogicCircuit::v128;
    QuadCircuit<Fp256Base> Q(p256_base);
    const CompilerBackend cbk(&Q);
    const LogicCircuit LC(&cbk, p256_base);
    using MACCircuit =
        MAC<LogicCircuit, BitPlucker<LogicCircuit, kMACPluckerBits>>;
    MACCircuit mac(LC);

    MACCircuit::Witness vwc[kNum];
    LogicCircuit::EltW msg[kNum];
    v128 mv[kNum][2];
    v128 a_v[kNum];
    for (size_t i = 0; i < kNum; ++i) {
      msg[i] = LC.eltw_input();
      mv[i][0] = LC.vinput<128>();
      mv[i][1] = LC.vinput<128>();
      a_v[i] = LC.vinput<128>();
    }

    Q.private_input();
    for (size_t i = 0; i < kNum; ++i) {
      vwc[i].input(LC);
    }
    for (size_t i = 0; i < kNum; ++i) {
      mac.verify_mac(msg[i], mv[i], a_v[i], vwc[i], n256_order);
    }

    circuit = Q.mkcircuit(1);
    dump_info("mac verify p256", Q);
    ninput = Q.ninput();
  }

  log(INFO, "Compile done");
  /*------------------------------------------------------------*/
  // Witness-creation time + fill inputs
  using gf2k = GF2_128<>::Elt;
  GF2_128<> gf;
  MACReference<GF2_128<>> mac_ref;
  SecureRandomEngine rng;

  uint8_t test_msg[32];

  for (size_t t = 0; t < 10; ++t) {
    rng.bytes(test_msg, 32);

    auto W = std::make_unique<Dense<Fp256Base>>(1, ninput);
    DenseFiller<Fp256Base> filler(*W);
    filler.push_back(p256_base.one());

    Fp256Base::Elt msg_elt = p256_base.of_bytes_field(test_msg).value();

    gf2k av, ap[2], mac[2];
    mac_ref.sample(&av, 1, &rng);
    mac_ref.sample(ap, 2, &rng);
    mac_ref.compute(mac, av, ap, test_msg);

    MacWitness<Fp256Base> vw(p256_base, gf);
    vw.compute_witness(ap, test_msg);

    for (size_t i = 0; i < kNum; ++i) {
      filler.push_back(msg_elt);

      // Fill inputs
      for (size_t j = 0; j < 2; ++j) {
        fill_gf2k<GF2_128<>, Fp256Base>(mac[j], filler, p256_base);
      }
      fill_gf2k<GF2_128<>, Fp256Base>(av, filler, p256_base);
    }

    for (size_t i = 0; i < kNum; ++i) {
      vw.fill_witness(filler);
    }

    log(INFO, "Fill done");
    /*------------------------------------------------------------*/
    // Prove
    Proof<Fp256Base> proof(circuit->nl);
    run_prover<Fp256Base>(circuit.get(), W->clone(), &proof, p256_base);

    log(INFO, "Prover done");
    /*------------------------------------------------------------*/
    // Verify
    run_verifier<Fp256Base>(circuit.get(), std::move(W), proof, p256_base);
    log(INFO, "Verify done");
  }
}

TEST(MAC, full_circuit_GF2_128) {
  set_log_level(INFO);
  using f_128 = GF2_128<>;
  size_t ninput;
  std::unique_ptr<Circuit<f_128>> circuit;
  f_128 F;
  FILE *test_vector = fopen("/tmp/test_vector.json", "w+");
  FILE *circuit_serialization = fopen("/tmp/longfellow-mac-circuit.circuit", "w+");
  FILE *sumcheck_proof = fopen("/tmp/longfellow-mac-circuit.sumcheck-proof", "w+");
  FILE *ligero_proof = fopen("/tmp/longfellow-mac-circuit.ligero-proof", "w+");
  if (test_vector == nullptr || circuit_serialization == nullptr
      || sumcheck_proof == nullptr || ligero_proof == nullptr) {
    fprintf(test_vector, "failed to open test vector file: %s\n", strerror(errno));
    return;
  }

  /*scope to delimit compile-time*/ {
    using CompilerBackend = CompilerBackend<f_128>;
    using LogicCircuit = Logic<f_128, CompilerBackend>;
    using EltW = LogicCircuit::EltW;
    using v256 = LogicCircuit::v256;
    QuadCircuit<f_128> Q(F);
    const CompilerBackend cbk(&Q);
    const LogicCircuit LC(&cbk, F);
    using MACCircuit =
        MACGF2<CompilerBackend, BitPlucker<LogicCircuit, kMACPluckerBits>>;
    MACCircuit mac(LC);
    MACCircuit::Witness vwc;

    v256 msg = LC.vinput<256>();
    EltW mv[2] = {LC.eltw_input(), LC.eltw_input()};
    EltW a_v = LC.eltw_input();
    Q.private_input();
    vwc.input(LC);
    mac.verify_mac(mv, a_v, msg, vwc);

    circuit = Q.mkcircuit(1);
    dump_info("mac_gf2_128 verify", Q);
    ninput = Q.ninput();
  }

  log(INFO, "Compile done");

  // Serialize the circuit.
  std::vector<uint8_t> bytes;
  CircuitRep<f_128> cr(F, GF2_128_ID);
  cr.to_bytes(*circuit, bytes);
  dump_to_file(circuit_serialization, bytes);

  fprintf(test_vector, "\"description\": \"Evaluates a MAC\",\n");
  fprintf(test_vector, "\"field\": %d,\n", GF2_128_ID);
  fprintf(test_vector, "\"depth\": %zu,\n", circuit->nl + 1);
  fprintf(test_vector, "\"quads\": %zu,\n", circuit->nterms());

  /*------------------------------------------------------------*/
  // Witness-creation time + fill inputs
  using gf2k = f_128::Elt;
  MACReference<f_128> mac_ref;
  SecureRandomEngine rng;

  uint8_t test_msg[32];

  for (size_t test_index = 0; test_index < 1; ++test_index) {
    rng.bytes(test_msg, 32);

    auto W = std::make_unique<Dense<f_128>>(1, ninput);
    DenseFiller<f_128> filler(*W);
    filler.push_back(F.one());

    for (size_t i = 0; i < 256; ++i) {
      filler.push_back((test_msg[i / 8] >> (i % 8) & 0x1) ? F.one() : F.zero());
    }

    gf2k av, ap[2], mac[2];
    mac_ref.sample(&av, 1, &rng);
    mac_ref.sample(ap, 2, &rng);
    mac_ref.compute(mac, av, ap, test_msg);

    MacGF2Witness vw;
    vw.compute_witness(ap);

    // Fill inputs
    for (size_t i = 0; i < 2; ++i) {
      filler.push_back(mac[i]);
    }
    filler.push_back(av);
    vw.fill_witness(filler);

    log(INFO, "Fill done");
    /*------------------------------------------------------------*/

    fprintf(test_vector, "\"valid_inputs\": [\n");
    std::vector<uint8_t> buf(F.kBytes);
    // skip the 1 prepended to inputs
    for (size_t i = 1; i < W->v_.size(); i++) {
      F.to_bytes_field(&buf[0], W->v_[i]);
      fprintf(test_vector, "    \"");
      dump_hex_to_file(test_vector, buf);
      fprintf(test_vector, "\"");
      if (i + 1 != W->v_.size()) {
        fprintf(test_vector, ",");
      }
      fprintf(test_vector, "\n");
    }
    fprintf(test_vector, "],\n"); // valid_inputs

    fprintf(test_vector, "\"invalid_inputs\": [\n");
    // skip the 1 prepended to inputs
    for (size_t i = 1; i < W->v_.size(); i++) {
      bool is_last = i + 1 == W->v_.size();
      auto elt = W->v_[i];
      if (is_last) {
        // tamper the last input so that the MAC won't validate
        F.add(elt, F.one());
      }
      F.to_bytes_field(&buf[0], elt);
      fprintf(test_vector, "    \"");
      dump_hex_to_file(test_vector, buf);
      fprintf(test_vector, "\"");
      if (!is_last) {
        fprintf(test_vector, ",");
      }
      fprintf(test_vector, "\n");
    }
    fprintf(test_vector, "],\n"); // invalid_inputs

    // ZK prove
    Transcript transcript((uint8_t *)"test", 4);
    TestRandomEngine rng;
    // The dummy random value used in TestRandomEngine
    fprintf(test_vector, "\"pad\": 2,\n");
    const LCH14ReedSolomonFactory reed_solomon_factory(F);

    ZkProof<f_128> mac_zk_proof(*circuit, kLigeroRate, kLigeroNreq);
    ZkProver<f_128, LCH14ReedSolomonFactory<f_128>> mac_zk_prover(*circuit, F, reed_solomon_factory);
    mac_zk_prover.commit(mac_zk_proof, *W, transcript, rng);
    EXPECT_TRUE(mac_zk_prover.prove(mac_zk_proof, *W, transcript));

    log(INFO, "Prover done");

    fprintf(test_vector, "\"ligero_parameters\": {\n");
    fprintf(test_vector, "    \"nreq\": %zu,\n", mac_zk_proof.param.nreq);
    fprintf(test_vector, "    \"rate\": %zu,\n", mac_zk_proof.param.rateinv);
    fprintf(test_vector, "    \"witnesses_per_row\": %zu,\n", mac_zk_proof.param.w);
    // this is wrong
    fprintf(test_vector, "    \"quadratic_constraints_per_row\": %zu,\n", mac_zk_proof.param.w);
    fprintf(test_vector, "    \"block_size\": %zu,\n", mac_zk_proof.param.block);
    fprintf(test_vector, "    \"num_columns\": %zu\n", mac_zk_proof.param.block_enc);
    fprintf(test_vector, "},\n"); // ligero_parameters

    std::vector<uint8_t> sumcheck_proof_bytes;
    mac_zk_proof.write_sc_proof(mac_zk_proof.proof, sumcheck_proof_bytes, F);
    dump_to_file(sumcheck_proof, sumcheck_proof_bytes);

    std::vector<uint8_t> commitment_bytes;
    mac_zk_proof.write_com(mac_zk_proof.com, commitment_bytes, F);
    fprintf(test_vector, "\"ligero_commitment\": \"");
    dump_hex_to_file(test_vector, commitment_bytes);
    fprintf(test_vector, "\",\n");

    fprintf(test_vector, "\"constraints\": {\n");
    fprintf(test_vector, "    \"linear_rhs\": [\n");
    for (size_t i = 0; i < mac_zk_prover.linear_constraint_rhs_.size(); i++) {
      F.to_bytes_field(&buf[0], mac_zk_prover.linear_constraint_rhs_[i]);
      fprintf(test_vector, "        \"");
      dump_hex_to_file(test_vector,buf);
      fprintf(test_vector, "\"");
      if (i + 1 != mac_zk_prover.linear_constraint_rhs_.size()) {
          fprintf(test_vector, ",");
      }
      fprintf(test_vector, "\n");
    }
    fprintf(test_vector, "    ],\n"); // linear_rhs
    fprintf(test_vector, "    \"quadratic\": [\n");
    for (size_t i = 0; i < mac_zk_prover.lqc_.size(); i++) {
      fprintf(test_vector, "        { \"x\": %zu, \"y\": %zu, \"z\": %zu }", mac_zk_prover.lqc_[i].x, mac_zk_prover.lqc_[i].y,
             mac_zk_prover.lqc_[i].z);
      if (i + 1 != mac_zk_prover.lqc_.size()) {
        fprintf(test_vector, ",");
      }
      fprintf(test_vector, "\n  ");
    }
    fprintf(test_vector, "    ]\n"); // quadratic
    fprintf(test_vector, "}\n"); // constraints

    std::vector<uint8_t> ligero_bytes;
    mac_zk_proof.write_com_proof(mac_zk_proof.com_proof, ligero_bytes, F);
    dump_to_file(ligero_proof, ligero_bytes);
  }

  fclose(test_vector);
}

}  // namespace
}  // namespace proofs
