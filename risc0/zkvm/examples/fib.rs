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

use std::sync::Arc;

use clap::Parser;
use risc0_zkvm::{
    get_prover_server, ExecutorEnv, ExecutorImpl, ProverOpts, ProverServer, VerifierContext,
};
use risc0_zkvm_methods::FIB_ELF;
use tracing_subscriber::{prelude::*, EnvFilter};

#[derive(Parser)]
struct Args {
    /// Number of iterations.
    #[arg(short, long)]
    iterations: u32,

    /// Specify the hash function to use.
    #[arg(short = 'f', long)]
    hashfn: Option<String>,

    /// Enable tracing forest
    #[arg(short, long, default_value_t = false)]
    tree: bool,

    #[arg(short, long, default_value_t = false)]
    skip_prover: bool,
}

#[derive(Debug)]
#[allow(unused)]
struct Metrics {
    segments: usize,
    user_cycles: u64,
    total_cycles: u64,
    seal: usize,
}

fn main() {
    let args = Args::parse();

    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(EnvFilter::from_default_env())
        .with(if args.tree {
            Some(tracing_forest::ForestLayer::default())
        } else {
            None
        })
        .init();

    let mut opts = ProverOpts::default();
    if let Some(hashfn) = args.hashfn {
        opts.hashfn = hashfn;
    }
    let prover = get_prover_server(&opts).unwrap();
    let metrics = top(prover, args.iterations, args.skip_prover);
    println!("{metrics:?}");
}

#[tracing::instrument(skip_all)]
fn top(prover: Arc<dyn ProverServer>, iterations: u32, skip_prover: bool) -> Metrics {
    let env = ExecutorEnv::builder()
        .write_slice(&[iterations])
        .build()
        .unwrap();
    let mut exec = ExecutorImpl::from_elf(env, FIB_ELF).unwrap();
    let session = exec.run().unwrap();
    let seal = if skip_prover {
        0
    } else {
        let ctx = VerifierContext::default();
        prover
            .prove_session(&ctx, &session)
            .unwrap()
            .inner
            .composite()
            .unwrap()
            .segments
            .iter()
            .fold(0, |acc, segment| acc + segment.get_seal_bytes().len())
    };

    Metrics {
        segments: session.segments.len(),
        user_cycles: session.user_cycles,
        total_cycles: session.total_cycles,
        seal,
    }
}
