
use super::*;

//
//Index Ops
//

//Currently, we just to indexing wrt `usize`. There may be additions in the future, but
//unlike with Matrices or slices, ranges don't really make much sense, and while indexing wrt
//basis blades _may_ make sense, it's slow *and* we have to deal with a potential minus sign.


macro_rules! impl_index {
    (impl<T:$Alloc:ident, $($N:ident),*> Index for $Ty:ident {}) => {

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Index<usize> for $Ty<T,$($N),*> {
            type Output = T;
            fn index(&self, i: usize) -> &T { &self.data[i] }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> IndexMut<usize> for $Ty<T,$($N),*> {
            fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
        }

    }
}

impl_index!(impl<T:AllocBlade, N, G> Index for Blade {});
impl_index!(impl<T:AllocRotor, N> Index for Rotor {});
impl_index!(impl<T:AllocMultivector, N> Index for Multivector {});

//
//Addition and Subtraction
//

//we do this as a macro to make it easier to do with self and rhs being both references and
//values in the macro calls
macro_rules! check {
    ($self:ident, $rhs:ident, Blade) => {

        //for ease of use
        let (d1, d2) = ($self.dim_generic(), $rhs.dim_generic());
        let (g1, g2) = ($self.grade_generic(), $rhs.grade_generic());

        //if the dims or grades don't match, panic
        //this check should optimize away for statically allocated blades
        //TODO: maybe have blades with same grade but different dim add together once we
        //have specialization and can use `Zero` conditionally
        if d1!=d2 { panic!("Cannot add blades of different dimension: {}!={}", d1.value(), d2.value()); }
        if g1!=g2 { panic!("Cannot add blades of different grade: {}!={}", g1.value(), g2.value()); }

    };

    ($self:ident, $rhs:ident, $Ty:ident) => {

        //for ease of use
        let (d1, d2) = ($self.dim_generic(), $rhs.dim_generic());

        //if the dims or grades don't match, panic
        //this check should optimize away for statically allocated values
        //TODO: maybe allow non-equal dims in the future
        if d1!=d2 { panic!("Cannot add blades of different dimension: {}!={}", d1.value(), d2.value()); }

    };
}

macro_rules! uninit {
    ($x:ident, AllocateBlade<$($T:ident),*>) => {
        AllocateBlade::<$($T),*>::uninit($x.dim_generic(), $x.grade_generic())
    };
    ($x:ident, $Allocate:ident<$($T:ident),*>) => {
        $Allocate::<$($T),*>::uninit($x.dim_generic())
    };
}

macro_rules! impl_binops {

    //implements operation with optional references
    (
        impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Allocate:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1,T2,U,$($N:Dim),*> $Op<$(&$b)? $Ty<T2,$($N),*>> for $(&$a)? $Ty<T1,$($N),*>
        where
            T1: $Alloc<$($N),*>,
            T2: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            $(&$a)? T1: $Op<$(&$b)? T2, Output=U>
        {

            type Output = $Ty<U,$($N),*>;

            fn $op(self, rhs: $(&$b)? $Ty<T2,$($N),*>) -> $Ty<U,$($N),*> {

                check!(self, rhs, $Ty);

                let mut dest = uninit!(self, $Allocate<U,$($N),*>);
                for ((t1, t2), u) in self.into_iter().zip(rhs).zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op(t2));
                }

                $Ty { data: unsafe { dest.assume_init() } }

            }

        }

    };

    //do every combination of reference and value
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Allocate:ident) => {
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate;   ;   );
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate; 'a;   );
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate;   ; 'b);
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate; 'a; 'b);
    };

}

macro_rules! impl_assign_binops {

    //implements operation with an optional reference
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident; $($a:lifetime)?) => {

        impl<$($a,)? T1, T2, $($N:Dim),*> $Op<$(&$a)? $Ty<T2,$($N),*>> for $Ty<T1,$($N),*>
        where
            T1: $Alloc<$($N),*> + $Op<$(&$a)? T2>,
            T2: $Alloc<$($N),*>
        {

            fn $op(&mut self, rhs: $(&$a)? $Ty<T2,$($N),*>) {

                check!(self, rhs, $Ty);

                //simple enough...
                for (t1, t2) in self.iter_mut().zip(rhs) {
                    t1.$op(t2);
                }

            }

        }

    };

    //do for value and reference
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident) => {
        impl_assign_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty;   );
        impl_assign_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty; 'a);
    };

}

impl_binops!(impl<T:AllocBlade,N,G> Add.add() for Blade with AllocateBlade);
impl_binops!(impl<T:AllocBlade,N,G> Sub.sub() for Blade with AllocateBlade);
impl_binops!(impl<T:AllocRotor,N> Add.add() for Rotor with AllocateRotor);
impl_binops!(impl<T:AllocRotor,N> Sub.sub() for Rotor with AllocateRotor);
impl_binops!(impl<T:AllocMultivector,N> Add.add() for Multivector with AllocateMultivector);
impl_binops!(impl<T:AllocMultivector,N> Sub.sub() for Multivector with AllocateMultivector);

impl_assign_binops!(impl<T:AllocBlade,N,G> AddAssign.add_assign() for Blade);
impl_assign_binops!(impl<T:AllocBlade,N,G> SubAssign.sub_assign() for Blade);
impl_assign_binops!(impl<T:AllocRotor,N> AddAssign.add_assign() for Rotor);
impl_assign_binops!(impl<T:AllocRotor,N> SubAssign.sub_assign() for Rotor);
impl_assign_binops!(impl<T:AllocMultivector,N> AddAssign.add_assign() for Multivector);
impl_assign_binops!(impl<T:AllocMultivector,N> SubAssign.sub_assign() for Multivector);

//TODO do Sum

//
//Zero
//

//currently, this only works with static allocation, but once we have specialization and
//can implement addition between dynamics with different dimensions, we can change that

impl<T:AllocBlade<N,G>+Zero, N:DimName, G:DimName> Zero for Blade<T,N,G> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
}

impl<T:AllocRotor<N>+Zero, N:DimName> Zero for Rotor<T,N> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
}

impl<T:AllocMultivector<N>+Zero, N:DimName> Zero for Multivector<T,N> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
}

//
//Neg
//

macro_rules! impl_unary_ops {
    (
        impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Allocate:ident;
        $($a:lifetime)?
    ) => {
        impl<$($a,)? T, U, $($N:Dim),*> $Op for $(&$a)? $Ty<T,$($N),*>
        where
            T: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            $(& $a)? T: $Op<Output=U>
        {

            type Output = $Ty<U,$($N),*>;

            fn $op(self) -> $Ty<U,$($N),*> {
                let mut dest = uninit!(self, $Allocate<U,$($N),*>);
                for (t, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t.$op());
                }

                $Ty { data: unsafe { dest.assume_init() } }
            }

        }

    };

    //do for value and reference
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Allocate:ident) => {
        impl_unary_ops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate;   );
        impl_unary_ops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Allocate; 'a);
    };
}

impl_unary_ops!(impl<T:AllocBlade,N,G> Neg.neg() for Blade with AllocateBlade);
impl_unary_ops!(impl<T:AllocRotor,N> Neg.neg() for Rotor with AllocateRotor);
impl_unary_ops!(impl<T:AllocMultivector,N> Neg.neg() for Multivector with AllocateMultivector);

//
//Scalar Multiplication and Division
//

macro_rules! impl_scale {

    (
        $(
            $(#[$meta:meta])*
            fn $fun:ident<U:$Alloc:ident,$($N:ident),*>() -> $(&$a:lifetime)? $Ty:ident with
                $Op:ident.$op:ident, $Allocate:ident {}
        )*
    ) => {

        $(
            $(#[$meta])*
            pub fn $fun<$($a,)? T2:Clone,U>($(&$a)? self, rhs:T2) -> $Ty<U,$($N),*> where
                $(&$a)? T1: $Op<T2,Output=U>,
                U: $Alloc<$($N),*>
            {
                let mut dest = uninit!(self, $Allocate<U,$($N),*>);
                for (t1, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op(rhs.clone()));
                }

                $Ty { data: unsafe { dest.assume_init() } }
            }
        )*

    };
}

//TODO: scale doc tests

macro_rules! scale_docs {
    ($kind:literal, $op:literal, $operate:literal, $operation:literal) => {
        concat!(
            $operate, " this ", $kind, " by a scalar\n",
            "\n",
            "Unlike with the `", $op, "` operator, this allows for ", $operation, "by scalars other",
            "than `T`, which is necessary to use some libraries (such as `dimensioned`)"
        )
    }
}

impl<T1:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T1,N,G> {

    impl_scale!(

        #[doc = scale_docs!("blade", "*", "Multiplies", "multiplication")]
        fn scale<U:AllocBlade,N,G>() -> Blade with Mul.mul, AllocateBlade {}

        #[doc = scale_docs!("blade", "*", "Multiplies", "multiplication")]
        fn scale_ref<U:AllocBlade,N,G>() -> &'a Blade with Mul.mul, AllocateBlade {}

        #[doc = scale_docs!("blade", "/", "Divides", "division")]
        fn inv_scale<U:AllocBlade,N,G>() -> Blade with Div.div, AllocateBlade {}

        #[doc = scale_docs!("blade", "/", "Divides", "division")]
        fn inv_scale_ref<U:AllocBlade,N,G>() -> &'a Blade with Div.div, AllocateBlade {}

    );

}

impl<T1:AllocRotor<N>, N:Dim> Rotor<T1,N> {

    impl_scale!(

        #[doc = scale_docs!("rotor", "*", "Multiplies", "multiplication")]
        fn scale<U:AllocRotor,N>() -> Rotor with Mul.mul, AllocateRotor {}

        #[doc = scale_docs!("rotor", "*", "Multiplies", "multiplication")]
        fn scale_ref<U:AllocRotor,N>() -> &'a Rotor with Mul.mul, AllocateRotor {}

        #[doc = scale_docs!("rotor", "/", "Divides", "division")]
        fn inv_scale<U:AllocRotor,N>() -> Rotor with Div.div, AllocateRotor {}

        #[doc = scale_docs!("rotor", "/", "Divides", "division")]
        fn inv_scale_ref<U:AllocRotor,N>() -> &'a Rotor with Div.div, AllocateRotor {}

    );

}

impl<T1:AllocMultivector<N>, N:Dim> Multivector<T1,N> {

    impl_scale!(

        #[doc = scale_docs!("multivector", "*", "Multiplies", "multiplication")]
        fn scale<U:AllocMultivector,N>() -> Multivector with Mul.mul, AllocateMultivector {}

        #[doc = scale_docs!("multivector", "*", "Multiplies", "multiplication")]
        fn scale_ref<U:AllocMultivector,N>() -> &'a Multivector with Mul.mul, AllocateMultivector {}

        #[doc = scale_docs!("multivector", "/", "Divides", "division")]
        fn inv_scale<U:AllocMultivector,N>() -> Multivector with Div.div, AllocateMultivector {}

        #[doc = scale_docs!("multivector", "/", "Divides", "division")]
        fn inv_scale_ref<U:AllocMultivector,N>() -> &'a Multivector with Div.div, AllocateMultivector {}

    );

}

macro_rules! impl_scalar_ops {

    (
        impl<T:$Alloc:ident, $($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $scale:ident;
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T,U,$($N:Dim),*> $Op<$(&$b)? T> for $(&$a)? $Ty<T,$($N),*>
        where
            T: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            $(&$a)? T: $Op<$(&$b)? T, Output=U>,
            $(&$b)? T: Clone
        {

            type Output = $Ty<U,$($N),*>;

            fn $op(self, t2: $(&$b)? T) -> $Ty<U,$($N),*> {
                self.$scale(t2)
            }

        }

    };

    //do every combination of reference and value
    (
        impl<T:$Alloc:ident, $($N:ident),*> $Op:ident.$op:ident() for $Ty:ident
        with $scale:ident, $scale_ref:ident
    ) => {
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op() for $Ty with $scale    ;   ;   );
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op() for $Ty with $scale_ref; 'a;   );
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op() for $Ty with $scale    ;   ; 'b);
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op() for $Ty with $scale_ref; 'a; 'b);
    };

}

impl_scalar_ops!(impl<T:AllocBlade,N,G> Mul.mul() for Blade with scale, scale_ref);
impl_scalar_ops!(impl<T:AllocBlade,N,G> Div.div() for Blade with inv_scale, inv_scale_ref);
impl_scalar_ops!(impl<T:AllocRotor,N> Mul.mul() for Rotor with scale, scale_ref);
impl_scalar_ops!(impl<T:AllocRotor,N> Div.div() for Rotor with inv_scale, inv_scale_ref);
impl_scalar_ops!(impl<T:AllocMultivector,N> Mul.mul() for Multivector with scale, scale_ref);
impl_scalar_ops!(impl<T:AllocMultivector,N> Div.div() for Multivector with inv_scale, inv_scale_ref);

macro_rules! impl_scalar_assign_binops {
    (impl<T:$Alloc:ident, $($N:ident),*> $Op:ident.$op:ident() for $Ty:ident) => {

        impl<T1:$Alloc<$($N),*>+$Op<T2>, T2:Clone, $($N:Dim),*> $Op<T2> for $Ty<T1, $($N),*> {
            fn $op(&mut self, rhs: T2) {
                //simple enough...
                for t1 in self {
                    t1.$op(rhs.clone());
                }
            }
        }

    }
}

impl_scalar_assign_binops!(impl<T:AllocBlade,N,G> MulAssign.mul_assign() for Blade);
impl_scalar_assign_binops!(impl<T:AllocBlade,N,G> DivAssign.div_assign() for Blade);
impl_scalar_assign_binops!(impl<T:AllocRotor,N> MulAssign.mul_assign() for Rotor);
impl_scalar_assign_binops!(impl<T:AllocRotor,N> DivAssign.div_assign() for Rotor);
impl_scalar_assign_binops!(impl<T:AllocMultivector,N> MulAssign.mul_assign() for Multivector);
impl_scalar_assign_binops!(impl<T:AllocMultivector,N> DivAssign.div_assign() for Multivector);
