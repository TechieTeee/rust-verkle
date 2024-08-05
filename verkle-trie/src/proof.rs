use crate::{
    constants::{CRS, PRECOMPUTED_WEIGHTS, VERKLE_NODE_WIDTH},
    errors::HintError,
};

use banderwagon::Element;
use ipa_multipoint::multiproof::MultiPointProof;
use ipa_multipoint::transcript::Transcript;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read, Write};

pub mod golang_proof_format;
mod key_path_finder;
mod opening_data;
pub(crate) mod prover;
pub mod stateless_updater;
pub(crate) mod verifier;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtPresent {
    None,
    DifferentStem,
    Present,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationHint {
    pub depths: Vec<u8>,
    pub extension_present: Vec<ExtPresent>,
    pub diff_stem_no_proof: BTreeSet<[u8; 31]>,
}

impl std::fmt::Display for VerificationHint {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for d in &self.depths {
            write!(f, "{} ", d)?;
        }
        for e in &self.extension_present {
            write!(f, "{:?} ", e)?;
        }
        for s in &self.diff_stem_no_proof {
            write!(f, "{} ", hex::encode(s))?;
        }
        Ok(())
    }
}

impl VerificationHint {
    pub fn read<R: Read>(mut reader: R) -> Result<Self, HintError> {
        let mut num_stems = [0u8; 4];
        reader.read_exact(&mut num_stems)?;
        let num_stems = u32::from_le_bytes(num_stems);

        let mut diff_stem_no_proof = BTreeSet::new();
        for _ in 0..num_stems {
            let mut stem = [0u8; 31];
            reader.read_exact(&mut stem)?;
            diff_stem_no_proof.insert(stem);
        }

        let mut num_depths = [0u8; 4];
        reader.read_exact(&mut num_depths)?;
        let num_depths = u32::from_le_bytes(num_depths) as usize;

        let mut depths = Vec::with_capacity(num_depths);
        let mut extension_present = Vec::with_capacity(num_depths);

        let mut buffer = vec![0u8; num_depths];
        reader.read_exact(&mut buffer)?;

        for &byte in &buffer {
            const MASK: u8 = 3;
            let ext_status = match byte & MASK {
                0 => ExtPresent::None,
                1 => ExtPresent::DifferentStem,
                2 => ExtPresent::Present,
                x => return Err(HintError::from(std::io::Error::new(std::io::ErrorKind::InvalidData, format!("unexpected ext status number {}", x)))),
            };
            depths.push(byte >> 3);
            extension_present.push(ext_status);
        }

        Ok(Self {
            depths,
            extension_present,
            diff_stem_no_proof,
        })
    }

    pub fn write<W: Write>(&self, writer: &mut W) -> Result<(), HintError> {
        writer.write_all(&(self.diff_stem_no_proof.len() as u32).to_le_bytes())?;
        for stem in &self.diff_stem_no_proof {
            writer.write_all(stem)?;
        }

        writer.write_all(&(self.depths.len() as u32).to_le_bytes())?;
        for (&depth, &ext_status) in self.depths.iter().zip(&self.extension_present) {
            let byte = match ext_status {
                ExtPresent::None => depth << 3,
                ExtPresent::DifferentStem => 1 | (depth << 3),
                ExtPresent::Present => 2 | (depth << 3),
            };
            writer.write_all(&[byte])?;
        }

        Ok(())
    }
}

pub struct UpdateHint {
    depths_and_ext_by_stem: BTreeMap<[u8; 31], (ExtPresent, u8)>,
    commitments_by_path: BTreeMap<Vec<u8>, Element>,
    other_stems_by_prefix: BTreeMap<Vec<u8>, [u8; 31]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerkleProof {
    pub verification_hint: VerificationHint,
    pub comms_sorted: Vec<Element>,
    pub proof: MultiPointProof,
}

impl VerkleProof {
    pub fn read<R: Read>(mut reader: R) -> Result<Self, HintError> {
        let verification_hint = VerificationHint::read(&mut reader)?;

        let mut num_comms = [0u8; 4];
        reader.read_exact(&mut num_comms)?;
        let num_comms = u32::from_le_bytes(num_comms) as usize;

        let mut comms_sorted = Vec::with_capacity(num_comms);
        for _ in 0..num_comms {
            let mut comm_serialized = [0u8; 32];
            reader.read_exact(&mut comm_serialized)?;
            let point = Element::from_bytes(&comm_serialized).ok_or_else(|| {
                HintError::from(std::io::Error::from(std::io::ErrorKind::InvalidData))
            })?;
            comms_sorted.push(point);
        }

        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes)?;
        let proof = MultiPointProof::from_bytes(&bytes, VERKLE_NODE_WIDTH)?;

        Ok(Self {
            verification_hint,
            comms_sorted,
            proof,
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> Result<(), HintError> {
        self.verification_hint.write(&mut writer)?;

        writer.write_all(&(self.comms_sorted.len() as u32).to_le_bytes())?;
        for comm in &self.comms_sorted {
            writer.write_all(&comm.to_bytes())?;
        }

        writer.write_all(&self.proof.to_bytes()?)?;
        Ok(())
    }

    pub fn check(
        self,
        keys: Vec<[u8; 32]>,
        values: Vec<Option<[u8; 32]>>,
        root: Element,
    ) -> (bool, Option<UpdateHint>) {
        let proof = self.proof.clone();
        let (queries, update_hint) = match verifier::create_verifier_queries(self, keys, values, root) {
            Some((queries, update_hint)) => (queries, update_hint),
            None => return (false, None),
        };

        let mut transcript = Transcript::new(b"vt");
        let ok = proof.check(&CRS, &PRECOMPUTED_WEIGHTS, &queries, &mut transcript);

        (ok, Some(update_hint))
    }
}

impl std::fmt::Display for VerkleProof {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Verkle proof:")?;
        writeln!(f, " * verification hints: {}", self.verification_hint)?;
        write!(f, " * commitments: ")?;
        for comm in self.comms_sorted.iter().map(|comm| hex::encode(comm.to_bytes())) {
            write!(f, "{} ", comm)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::VerkleProof;
    use crate::database::{memory_db::MemoryDb, ReadOnlyHigherDb};
    use crate::proof::{prover, verifier};
    use crate::{trie::Trie, DefaultConfig, TrieTrait};
    use banderwagon::Fr;

    #[test]
    fn basic_proof_true() {
        let db = MemoryDb::new();
        let mut trie = Trie::new(DefaultConfig::new(db));

        let mut keys = Vec::new();
        for i in 0..=3 {
            let mut key_0 = [0u8; 32];
            key_0[0] = i;
            keys.push(key_0);
            trie.insert_single(key_0, key_0);
        }
        let root = vec![];
        let meta = trie.storage.get_branch_meta(&root).unwrap();

        let proof = prover::create_verkle_proof(&trie.storage, keys.clone()).unwrap();
        let values: Vec<_> = keys.iter().map(|val| Some(*val)).collect();
        let (ok, _) = proof.check(keys, values, meta.commitment);
        assert!(ok);
    }

    #[test]
    fn proof_of_absence_edge_case() {
        let db = MemoryDb::new();
        let trie = Trie::new(DefaultConfig::new(db));

        let absent_keys = vec![[3; 32]];
        let absent_values = vec![None];

        let root = vec![];
        let meta = trie.storage.get_branch_meta(&root).unwrap();
        let proof = prover::create_verkle_proof(&trie.storage, absent_keys.clone()).unwrap();
        let (ok, _) = proof.check(absent_keys, absent_values, meta.commitment);
        assert!(ok);
    }

    #[test]
    fn display_hint() {
        use crate::proof::{ExtPresent, VerificationHint};
        use std::collections::BTreeSet;

        let hint = VerificationHint {
            depths: vec![3],
            extension_present: vec![ExtPresent::DifferentStem],
            diff_stem_no_proof: {
                let mut stems = BTreeSet::new();
                stems.insert([1; 31]);
                stems
            },
        };
        assert_eq!(
            hint.to_string(),
            "3  DifferentStem  0101010101010101010101010101010101010101010101010101010101010101 "
        );
    }
}
