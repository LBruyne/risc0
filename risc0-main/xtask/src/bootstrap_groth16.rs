// Copyright 2024 RISC Zero, Inc.
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

use std::{fs, path::Path, process::Command};

use clap::Parser;
use hex::FromHex;
use regex::Regex;
use risc0_zkvm::{
    get_prover_server,
    recursion::identity_p254,
    sha::{Digest, Digestible},
    stark_to_snark, CompactReceipt, ExecutorEnv, ExecutorImpl, InnerReceipt, ProverOpts, Receipt,
    VerifierContext, ALLOWED_CONTROL_ROOT,
};
use risc0_zkvm_methods::{multi_test::MultiTestSpec, MULTI_TEST_ELF, MULTI_TEST_ID};

use crate::bootstrap::Bootstrap;

#[derive(Debug, Parser)]
pub struct BootstrapGroth16 {
    /// ris0-ethereum repository path
    #[arg(long, env)]
    risc0_ethereum_path: String,

    /// bootstrap test receipt only (exclude rust verifier and control id)
    #[arg(long, action = clap::ArgAction::SetTrue, default_value_t = false)]
    test_receipt_only: bool,
}

const SOL_HEADER: &str = r#"// Copyright 2024 RISC Zero, Inc.
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
//
// SPDX-License-Identifier: Apache-2.0

// This file is automatically generated by:
// cargo xtask bootstrap-groth16

"#;

const SOLIDITY_VERIFIER_SOURCE: &str = "compact_proof/groth16/verifier.sol";
const SOLIDITY_VERIFIER_TARGET: &str = "contracts/src/groth16/Groth16Verifier.sol";
const SOLIDITY_CONTROL_ID_PATH: &str = "contracts/src/groth16/ControlID.sol";
const SOLIDITY_TEST_RECEIPT_PATH: &str = "contracts/test/TestReceipt.sol";
const RUST_VERIFIER_PATH: &str = "risc0/groth16/src/verifier.rs";

impl BootstrapGroth16 {
    pub fn run(&self) {
        let current_dir = std::env::current_dir().unwrap();
        let risc0_ethereum_path = current_dir.join(&self.risc0_ethereum_path);
        if !self.test_receipt_only {
            bootstrap_verifying_key(&risc0_ethereum_path);
            bootstrap_control_id(&risc0_ethereum_path);
        }
        bootstrap_test_receipt(&risc0_ethereum_path);
    }
}

fn bootstrap_verifying_key(risc0_ethereum_path: &Path) {
    let solidity_verifier_target = risc0_ethereum_path.join(SOLIDITY_VERIFIER_TARGET);
    std::fs::copy(SOLIDITY_VERIFIER_SOURCE, solidity_verifier_target).unwrap();
    let solidity_code = fs::read_to_string(SOLIDITY_VERIFIER_SOURCE).unwrap();
    let mut rust_code = fs::read_to_string(RUST_VERIFIER_PATH).unwrap();

    let solidity_constants = [
        "alphax", "alphay", "betax1", "betax2", "betay1", "betay2", "gammax1", "gammax2",
        "gammay1", "gammay2", "deltax1", "deltax2", "deltay1", "deltay2", "IC0x", "IC0y", "IC1x",
        "IC1y", "IC2x", "IC2y", "IC3x", "IC3y", "IC4x", "IC4y", "IC5x", "IC5y",
    ];

    let rust_constants = [
        "ALPHA_X", "ALPHA_Y", "BETA_X1", "BETA_X2", "BETA_Y1", "BETA_Y2", "GAMMA_X1", "GAMMA_X2",
        "GAMMA_Y1", "GAMMA_Y2", "DELTA_X1", "DELTA_X2", "DELTA_Y1", "DELTA_Y2", "IC0_X", "IC0_Y",
        "IC1_X", "IC1_Y", "IC2_X", "IC2_Y", "IC3_X", "IC3_Y", "IC4_X", "IC4_Y", "IC5_X", "IC5_Y",
    ];

    for (i, constant) in solidity_constants.into_iter().enumerate() {
        let re = Regex::new(&format!(r"uint256 constant\s+{}\s*=\s*(\d+);", constant)).unwrap();
        if let Some(caps) = re.captures(&solidity_code) {
            let rust_re = Regex::new(&format!(
                "const {}: &str =[\\r\\n\\s]*\"\\d+\";",
                rust_constants[i]
            ))
            .unwrap();
            rust_code = rust_re
                .replace(
                    &rust_code,
                    &format!("const {}: &str = \"{}\";", rust_constants[i], &caps[1]),
                )
                .to_string();
        } else {
            println!("{} not found", constant);
        }
    }

    fs::write(RUST_VERIFIER_PATH, rust_code).unwrap();

    // Use rustfmt to format the file.
    Command::new("rustfmt")
        .arg(RUST_VERIFIER_PATH)
        .status()
        .expect("failed to format {RUST_GROTH16_VERIFIER_PATH}");
}

fn bootstrap_control_id(risc0_ethereum_path: &Path) {
    const LIB_HEADER: &str = r#"pragma solidity ^0.8.9;

 library ControlID {
"#;
    let (control_id_0, control_id_1) =
        split_digest(Digest::from_hex(ALLOWED_CONTROL_ROOT).unwrap());
    let bn254_control_id = format!("0x{}", Bootstrap::generate_identity_bn254_control_id());
    let control_id_0 = format!("uint256 public constant CONTROL_ID_0 = {control_id_0};");
    let control_id_1 = format!("uint256 public constant CONTROL_ID_1 = {control_id_1};");
    let bn254_control_id =
        format!("uint256 public constant BN254_CONTROL_ID = {bn254_control_id};");
    let content = &format!(
        "{SOL_HEADER}{LIB_HEADER}\n{control_id_0}\n{control_id_1}\n{bn254_control_id}\n}}"
    );
    let solidity_control_id_path = risc0_ethereum_path.join(SOLIDITY_CONTROL_ID_PATH);
    fs::write(&solidity_control_id_path, content).unwrap_or_else(|_| {
        panic!(
            "failed to save changes to {}",
            solidity_control_id_path.display()
        )
    });

    // Use forge fmt to format the file.
    Command::new("forge")
        .arg("fmt")
        .arg(solidity_control_id_path.as_os_str())
        .status()
        .unwrap_or_else(|_| panic!("failed to format {}", solidity_control_id_path.display()));
}

fn bootstrap_test_receipt(risc0_ethereum_path: &Path) {
    const LIB_HEADER: &str = r#"pragma solidity ^0.8.13;

 library TestReceipt {
"#;
    let (receipt, image_id) = generate_receipt();
    let seal = hex::encode(receipt.inner.compact().unwrap().seal.clone());
    let post_digest = format!(
        "0x{}",
        hex::encode(receipt.get_claim().unwrap().post.digest().as_bytes())
    );
    let image_id = format!("0x{}", hex::encode(image_id.as_bytes()));
    let journal = hex::encode(receipt.journal.bytes);

    let seal = format!("bytes public constant SEAL = hex\"{seal}\";");
    let post_digest = format!("bytes32 public constant POST_DIGEST = bytes32({post_digest});");
    let journal = format!("bytes public constant JOURNAL = hex\"{journal}\";");
    let image_id = format!("bytes32 public constant IMAGE_ID = bytes32({image_id});");

    let solidity_test_receipt_path = risc0_ethereum_path.join(SOLIDITY_TEST_RECEIPT_PATH);
    let content =
        &format!("{SOL_HEADER}{LIB_HEADER}\n{seal}\n{post_digest}\n{journal}\n{image_id}\n}}");
    fs::write(&solidity_test_receipt_path, content).unwrap();

    // Use forge fmt to format the file.
    Command::new("forge")
        .arg("fmt")
        .arg(solidity_test_receipt_path.as_os_str())
        .status()
        .unwrap();
}

// Splits the digest in half returning the two halves as big endian
fn split_digest(d: Digest) -> (String, String) {
    let big_endian: Vec<u8> = d.as_bytes().to_vec().iter().rev().cloned().collect();
    let middle = big_endian.len() / 2;
    let (control_id_1, control_id_0) = big_endian.split_at(middle);
    (
        format!("0x{}", hex::encode(control_id_0)),
        format!("0x{}", hex::encode(control_id_1)),
    )
}

// Return a Compact `Receipt` and the imageID used to generate the proof.
// Requires running Docker on an x86 architecture.
fn generate_receipt() -> (Receipt, Digest) {
    let env = ExecutorEnv::builder()
        .write(&MultiTestSpec::BusyLoop { cycles: 0 })
        .unwrap()
        .build()
        .unwrap();

    tracing::info!("execute");

    let mut exec = ExecutorImpl::from_elf(env, MULTI_TEST_ELF).unwrap();
    let session = exec.run().unwrap();

    tracing::info!("prove");
    let opts = ProverOpts::default();
    let ctx = VerifierContext::default();
    let prover = get_prover_server(&opts).unwrap();
    let receipt = prover.prove_session(&ctx, &session).unwrap().receipt;
    let claim = receipt.get_claim().unwrap();
    let composite_receipt = receipt.inner.composite().unwrap();
    let succinct_receipt = prover.compress(composite_receipt).unwrap();
    let journal = session.journal.unwrap().bytes;

    tracing::info!("identity_p254");
    let ident_receipt = identity_p254(&succinct_receipt).unwrap();
    let seal_bytes = ident_receipt.get_seal_bytes();

    tracing::info!("stark-to-snark");
    let seal = stark_to_snark(&seal_bytes).unwrap().to_vec();

    tracing::info!("Receipt");
    let compact_receipt = Receipt::new(
        InnerReceipt::Compact(CompactReceipt { seal, claim }),
        journal,
    );
    let image_id = Digest::from(MULTI_TEST_ID);
    (compact_receipt, image_id)
}
