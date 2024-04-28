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

use std::sync::{Arc, Mutex};
use std::thread;

use anyhow::{bail, Result};
use risc0_core::field::baby_bear::{BabyBear, Elem, ExtElem};
use risc0_zkp::hal::{CircuitHal, Hal};

use super::{HalPair, ProverServer};
use crate::{
    host::{
        client::prove::ReceiptKind,
        prove_info::ProveInfo,
        receipt::{
            CompactReceipt, CompositeReceipt, InnerReceipt, SegmentReceipt, SuccinctReceipt,
        },
        recursion::{identity_p254, join, lift, resolve},
    },
    sha::Digestible,
    stark_to_snark, Receipt, Segment, Session, VerifierContext,
};

/// An implementation of a Prover that runs locally.
pub struct ProverImpl<H, C>
where
    H: Hal<Field = BabyBear, Elem = Elem, ExtElem = ExtElem>,
    C: CircuitHal<H>,
{
    name: String,
    hal_pair: HalPair<H, C>,
    receipt_kind: ReceiptKind,
}

impl<H, C> ProverImpl<H, C>
where
    H: Hal<Field = BabyBear, Elem = Elem, ExtElem = ExtElem>,
    C: CircuitHal<H>,
{
    /// Construct a [ProverImpl] with the given name and [HalPair].
    pub fn new(name: &str, hal_pair: HalPair<H, C>, receipt_kind: ReceiptKind) -> Self {
        Self {
            name: name.to_string(),
            hal_pair,
            receipt_kind,
        }
    }
}



impl<H, C> ProverServer for ProverImpl<H, C>
where
    H: Hal<Field = BabyBear, Elem = Elem, ExtElem = ExtElem>,
    C: CircuitHal<H>,
{
    fn prove_session(&self, ctx: &VerifierContext, session: &Session) -> Result<ProveInfo> {
        println!(
            "prove_session: {}, exit_code = {:?}, journal = {:?}, segments: {}",
            self.name,
            session.exit_code,
            session.journal.as_ref().map(|x| hex::encode(x)),
            session.segments.len()
        );

        // let mut segments = Vec::new();
        // for segment_ref in session.segments.iter() {
        //     let segment = segment_ref.resolve()?;
        //     for hook in &session.hooks {
        //         hook.on_pre_prove_segment(&segment);
        //     }
        //     segments.push(self.prove_segment(ctx, &segment)?);
        //     for hook in &session.hooks {
        //         hook.on_post_prove_segment(&segment);
        //     }
        // }

        // 创建一个共享的 segments 向量
        let segments = Arc::new(Mutex::new(Vec::new()));

        // 创建一个向量用于存储线程句柄
        let mut handles = vec![];

        // 遍历 session.segments 的迭代器来处理每个 segment
        for segment_ref in session.segments.iter() {
            let segments = Arc::clone(&segments);

            // 使用线程来处理每个 segment
            let handle = thread::spawn(move || {
                let segment = segment_ref.resolve().unwrap(); // 或者适当处理错误
                for hook in &session.hooks {
                    hook.on_pre_prove_segment(&segment);
                }
                let proved_segment = self.prove_segment(ctx, &segment).unwrap(); // 或者适当处理错误

                // 将 proved_segment 放入共享的 segments 向量中
                let mut segments = segments.lock().unwrap();
                segments.push(proved_segment);

                for hook in &session.hooks {
                    hook.on_post_prove_segment(&segment);
                }
            });

            // 将线程句柄存入向量中
            handles.push(handle);
        }

        // 等待所有线程执行完毕
        for handle in handles {
            handle.join().unwrap();
        }

        let segments_mutex = Arc::clone(&segments);
        let segments = segments_mutex.lock().unwrap().clone();

        // TODO(#982): Support unresolved assumptions here.
        let assumptions = session
            .assumptions
            .iter()
            .map(|x| Ok(x.as_receipt()?.inner.clone()))
            .collect::<Result<Vec<_>>>()?;
        let composite_receipt = CompositeReceipt {
            segments,
            assumptions,
            journal_digest: session.journal.as_ref().map(|journal| journal.digest()),
        };

        // Verify the receipt to catch if something is broken in the proving process.
        composite_receipt.verify_integrity_with_context(ctx)?;
        if composite_receipt.get_claim()?.digest() != session.get_claim()?.digest() {
            println!("composite receipt and session claim do not match");
            println!(
                "composite receipt claim: {:#?}",
                composite_receipt.get_claim()?
            );
            println!("session claim: {:#?}", session.get_claim()?);
            bail!(
                "session and composite receipt claim do not match: session {}, receipt {}",
                hex::encode(&session.get_claim()?.digest()),
                hex::encode(&composite_receipt.get_claim()?.digest())
            );
        }

        let receipt = match self.receipt_kind {
            ReceiptKind::Composite => Receipt::new(
                InnerReceipt::Composite(composite_receipt),
                session.journal.clone().unwrap_or_default().bytes,
            ),
            ReceiptKind::Succinct => {
                let succinct_receipt = self.compress(&composite_receipt)?;
                Receipt::new(
                    InnerReceipt::Succinct(succinct_receipt),
                    session.journal.clone().unwrap_or_default().bytes,
                )
            }
            ReceiptKind::Compact => {
                let succinct_receipt = self.compress(&composite_receipt)?;
                let ident_receipt = identity_p254(&succinct_receipt).unwrap();
                let seal_bytes = ident_receipt.get_seal_bytes();
                let claim = session.get_claim()?;

                let seal = stark_to_snark(&seal_bytes)?.to_vec();
                Receipt::new(
                    InnerReceipt::Compact(CompactReceipt { seal, claim }),
                    session.journal.clone().unwrap_or_default().bytes,
                )
            }
        };

        // Verify the receipt to catch if something is broken in the proving process.
        receipt.verify_integrity_with_context(ctx)?;
        if receipt.get_claim()?.digest() != session.get_claim()?.digest() {
            println!("receipt and session claim do not match");
            println!("receipt claim: {:#?}", receipt.get_claim()?);
            println!("session claim: {:#?}", session.get_claim()?);
            bail!(
                "session and receipt claim do not match: session {}, receipt {}",
                hex::encode(&session.get_claim()?.digest()),
                hex::encode(&receipt.get_claim()?.digest())
            );
        }

        Ok(ProveInfo {
            receipt,
            stats: session.stats(),
        })
    }

    fn prove_segment(&self, ctx: &VerifierContext, segment: &Segment) -> Result<SegmentReceipt> {
        use risc0_circuit_rv32im::prove::{engine::SegmentProverImpl, SegmentProver as _};

        use crate::host::receipt::decode_receipt_claim_from_seal;

        let hashfn = self.hal_pair.hal.get_hash_suite().name.clone();

        let prover =
            SegmentProverImpl::new(self.hal_pair.hal.clone(), self.hal_pair.circuit_hal.clone());
        let seal = prover.prove_segment(&segment.inner)?;

        let mut claim = decode_receipt_claim_from_seal(&seal)?;
        claim.output = segment.output.clone().into();

        let receipt = SegmentReceipt {
            seal,
            index: segment.index as u32,
            hashfn,
            claim,
        };
        receipt.verify_integrity_with_context(ctx)?;

        Ok(receipt)
    }

    fn get_peak_memory_usage(&self) -> usize {
        self.hal_pair.hal.get_memory_usage()
    }

    fn lift(&self, receipt: &SegmentReceipt) -> Result<SuccinctReceipt> {
        lift(receipt)
    }

    fn join(&self, a: &SuccinctReceipt, b: &SuccinctReceipt) -> Result<SuccinctReceipt> {
        join(a, b)
    }

    fn resolve(
        &self,
        conditional: &SuccinctReceipt,
        assumption: &SuccinctReceipt,
    ) -> Result<SuccinctReceipt> {
        resolve(conditional, assumption)
    }

    fn identity_p254(&self, a: &SuccinctReceipt) -> Result<SuccinctReceipt> {
        identity_p254(a)
    }
}
