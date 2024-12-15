//! Orchard fixed bases.
use halo2_gadgets::ecc::{
    chip::{BaseFieldElem, FixedPoint, FullScalar, ShortScalar},
    FixedPoints,
};

use pasta_curves::pallas;

pub mod commit_ivk_r;
pub mod note_commit_r;
pub mod nullifier_k;
pub mod spend_auth_g;
pub mod value_commit_r;
pub mod value_commit_v;
pub mod gens_1;
pub mod gens_2;
pub mod gens_3;
pub mod gens_4;
pub mod gens_5;
pub mod gens_6;
pub mod gens_7;
pub mod gens_8;
pub mod gens_9;
pub mod gens_10;
pub mod gens_11;
pub mod gens_12;
pub mod gens_13;
pub mod gens_14;
pub mod gens_15;
pub mod gens_16;



pub(crate) const L_ORCHARD_SCALAR: usize = 255;
pub(crate) const L_VALUE: usize = 64;


/// SWU hash-to-curve personalization for the spending key base point and
/// the nullifier base point K^Orchard
pub const ORCHARD_PERSONALIZATION: &str = "z.cash:Orchard";

/// SWU hash-to-curve personalization for the value commitment generator
pub const VALUE_COMMITMENT_PERSONALIZATION: &str = "z.cash:Orchard-cv";

/// SWU hash-to-curve value for the value commitment generator
pub const VALUE_COMMITMENT_V_BYTES: [u8; 1] = *b"v";

/// SWU hash-to-curve value for the value commitment generator
pub const VALUE_COMMITMENT_R_BYTES: [u8; 1] = *b"r";

/// SWU hash-to-curve personalization for the note commitment generator
pub const NOTE_COMMITMENT_PERSONALIZATION: &str = "z.cash:Orchard-NoteCommit";

/// SWU hash-to-curve personalization for the IVK commitment generator
pub const COMMIT_IVK_PERSONALIZATION: &str = "z.cash:Orchard-CommitIvk";

/// Window size for fixed-base scalar multiplication
pub const FIXED_BASE_WINDOW_SIZE: usize = 3;

/// $2^{`FIXED_BASE_WINDOW_SIZE`}$
pub const H: usize = 1 << FIXED_BASE_WINDOW_SIZE;

/// Number of windows for a full-width scalar
pub const NUM_WINDOWS: usize =
    (L_ORCHARD_SCALAR + FIXED_BASE_WINDOW_SIZE - 1) / FIXED_BASE_WINDOW_SIZE;

/// Number of windows for a short signed scalar
pub const NUM_WINDOWS_SHORT: usize =
    (L_VALUE + FIXED_BASE_WINDOW_SIZE - 1) / FIXED_BASE_WINDOW_SIZE;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
// A sum type for both full-width and short bases. This enables us to use the
// shared functionality of full-width and short fixed-base scalar multiplication.
pub enum OrchardFixedBases {
    Full(OrchardFixedBasesFull),
    NullifierK,
    ValueCommitV,
}

impl From<OrchardFixedBasesFull> for OrchardFixedBases {
    fn from(full_width_base: OrchardFixedBasesFull) -> Self {
        Self::Full(full_width_base)
    }
}

impl From<ValueCommitV> for OrchardFixedBases {
    fn from(_value_commit_v: ValueCommitV) -> Self {
        Self::ValueCommitV
    }
}

impl From<NullifierK> for OrchardFixedBases {
    fn from(_nullifier_k: NullifierK) -> Self {
        Self::NullifierK
    }
}

/// The Orchard fixed bases used in scalar mul with full-width scalars.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum OrchardFixedBasesFull {
    CommitIvkR,
    NoteCommitR,
    ValueCommitR,
    SpendAuthG,
    gens_1,
    gens_2,
    gens_3,
    gens_4,
    gens_5,
    gens_6,
    gens_7,
    gens_8,
    gens_9,
    gens_10,
    gens_11,
    gens_12,
    gens_13,
    gens_14,
    gens_15,
    gens_16
}

/// NullifierK is used in scalar mul with a base field element.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct NullifierK;

/// ValueCommitV is used in scalar mul with a short signed scalar.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ValueCommitV;

impl FixedPoints<pallas::Affine> for OrchardFixedBases {
    type FullScalar = OrchardFixedBasesFull;
    type Base = NullifierK;
    type ShortScalar = ValueCommitV;
}

impl FixedPoint<pallas::Affine> for OrchardFixedBasesFull {
    type FixedScalarKind = FullScalar;

    fn generator(&self) -> pallas::Affine {
        match self {
            Self::CommitIvkR => commit_ivk_r::generator(),
            Self::NoteCommitR => note_commit_r::generator(),
            Self::ValueCommitR => value_commit_r::generator(),
            Self::SpendAuthG => spend_auth_g::generator(),
            Self::gens_1 => gens_1::generator(),
            Self::gens_2 => gens_2::generator(),
            Self::gens_3 => gens_3::generator(),
            Self::gens_4 => gens_4::generator(),
            Self::gens_5 => gens_5::generator(),
            Self::gens_6 => gens_6::generator(),
            Self::gens_7 => gens_7::generator(),
            Self::gens_8 => gens_8::generator(),
            Self::gens_9 => gens_9::generator(),
            Self::gens_10 => gens_10::generator(),
            Self::gens_11 => gens_11::generator(),
            Self::gens_12 => gens_12::generator(),
            Self::gens_13 => gens_13::generator(),
            Self::gens_14 => gens_14::generator(),
            Self::gens_15 => gens_15::generator(),
            Self::gens_16 => gens_16::generator(),
        }
    }

    fn u(&self) -> Vec<[[u8; 32]; H]> {
        match self {
            Self::CommitIvkR => commit_ivk_r::U.to_vec(),
            Self::NoteCommitR => note_commit_r::U.to_vec(),
            Self::ValueCommitR => value_commit_r::U.to_vec(),
            Self::SpendAuthG => spend_auth_g::U.to_vec(),
            Self::gens_1 => gens_1::U.to_vec(),
            Self::gens_2 => gens_2::U.to_vec(),
            Self::gens_3 => gens_3::U.to_vec(),
            Self::gens_4 => gens_4::U.to_vec(),
            Self::gens_5 => gens_5::U.to_vec(),
            Self::gens_6 => gens_6::U.to_vec(),
            Self::gens_7 => gens_7::U.to_vec(),
            Self::gens_8 => gens_8::U.to_vec(),
            Self::gens_9 => gens_9::U.to_vec(),
            Self::gens_10 => gens_10::U.to_vec(),
            Self::gens_11 => gens_11::U.to_vec(),
            Self::gens_12 => gens_12::U.to_vec(),
            Self::gens_13 => gens_13::U.to_vec(),
            Self::gens_14 => gens_14::U.to_vec(),
            Self::gens_15 => gens_15::U.to_vec(),
            Self::gens_16 => gens_16::U.to_vec(),
        }
    }

    fn z(&self) -> Vec<u64> {
        match self {
            Self::CommitIvkR => commit_ivk_r::Z.to_vec(),
            Self::NoteCommitR => note_commit_r::Z.to_vec(),
            Self::ValueCommitR => value_commit_r::Z.to_vec(),
            Self::SpendAuthG => spend_auth_g::Z.to_vec(),
            Self::gens_1 => gens_1::Z.to_vec(),
            Self::gens_2 => gens_2::Z.to_vec(),
            Self::gens_3 => gens_3::Z.to_vec(),
            Self::gens_4 => gens_4::Z.to_vec(),
            Self::gens_5 => gens_5::Z.to_vec(),
            Self::gens_6 => gens_6::Z.to_vec(),
            Self::gens_7 => gens_7::Z.to_vec(),
            Self::gens_8 => gens_8::Z.to_vec(),
            Self::gens_9 => gens_9::Z.to_vec(),
            Self::gens_10 => gens_10::Z.to_vec(),
            Self::gens_11 => gens_11::Z.to_vec(),
            Self::gens_12 => gens_12::Z.to_vec(),
            Self::gens_13 => gens_13::Z.to_vec(),
            Self::gens_14 => gens_14::Z.to_vec(),
            Self::gens_15 => gens_15::Z.to_vec(),
            Self::gens_16 => gens_16::Z.to_vec(),

        }
    }
}

impl FixedPoint<pallas::Affine> for NullifierK {
    type FixedScalarKind = BaseFieldElem;

    fn generator(&self) -> pallas::Affine {
        nullifier_k::generator()
    }

    fn u(&self) -> Vec<[[u8; 32]; H]> {
        nullifier_k::U.to_vec()
    }

    fn z(&self) -> Vec<u64> {
        nullifier_k::Z.to_vec()
    }
}

impl FixedPoint<pallas::Affine> for ValueCommitV {
    type FixedScalarKind = ShortScalar;

    fn generator(&self) -> pallas::Affine {
        value_commit_v::generator()
    }

    fn u(&self) -> Vec<[[u8; 32]; H]> {
        value_commit_v::U_SHORT.to_vec()
    }

    fn z(&self) -> Vec<u64> {
        value_commit_v::Z_SHORT.to_vec()
    }
}

// fn main() {
//     println!("testing");
// }
