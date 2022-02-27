//!
//! Items common to all subsystems
//!

pub use self::storage::*;
pub use self::alloc::*;
pub use self::dim::*;
pub use self::coordinates::*;
pub use self::ops::*;
pub use self::count::*;
pub use self::basis_blade::*;

pub mod storage;
pub mod alloc;
pub mod dim;
pub mod coordinates;
pub mod ops;

pub mod basis_blade {
    #[doc(inline)] pub use basis_blade::BasisBlade;
}

pub mod count {

    #[doc(inline)] pub use basis_blade::{
        binom, even_elements, odd_elements, multivector_elements,
        grade_index_in_versor, grade_index_in_multivector,
        components_of, even_components_of, odd_components_of
    };
}


// mod count;
// mod basis_blade;
