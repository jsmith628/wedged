
use super::*;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Subspace {
    Blade(usize, usize),
    Even(usize),
    Odd(usize),
    Full(usize)
}

impl Subspace {
    #[allow(dead_code)]
    pub(crate) fn dim(&self) -> usize {
        match self {
            Self::Blade(n,_) => *n,
            Self::Even(n) => *n,
            Self::Odd(n) => *n,
            Self::Full(n) => *n
        }
    }
}

pub(crate) trait MultivectorSrc:IntoIterator {

    type Scalar;
    type Dim: Dim;
    type Shape: Copy;

    fn dim(&self) -> Self::Dim;
    fn elements(&self) -> usize;
    fn subspace(&self) -> Subspace;
    fn shape(&self) -> Self::Shape;

    fn get(&self, i:usize) -> &Self::Scalar;
    fn basis(&self, i:usize) -> BasisBlade;
}

pub(crate) trait MultivectorDst: MultivectorSrc {

    type Uninit: UninitStorage<Self::Scalar>;

    fn subspace_of(shape: Self::Shape) -> Subspace;

    fn uninit(shape: Self::Shape) -> Self::Uninit;
    unsafe fn assume_init(uninit:Self::Uninit) -> Self;

    fn set(&mut self, i:usize, x: Self::Scalar);
    fn index_of(basis:BasisBlade, shape:Self::Shape) -> Option<(usize, bool)>;

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorSrc for Blade<T,N,G> {

    type Scalar = T;
    type Dim = N;
    type Shape = (N,G);

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Blade(Blade::dim(self), self.grade()) }
    fn elements(&self) -> usize { Blade::elements(self) }
    fn shape(&self) -> (N,G) { (self.dim_generic(), self.grade_generic()) }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_blade(Blade::dim(self), self.grade(), i)
    }

}

impl<T:AllocEven<N>, N:Dim> MultivectorSrc for Even<T,N> {

    type Scalar = T;
    type Dim = N;
    type Shape = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Even(Even::dim(self)) }
    fn elements(&self) -> usize { Even::elements(self) }
    fn shape(&self) -> N { self.dim_generic() }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_even(Even::dim(self), i)
    }

}

impl<T:AllocOdd<N>, N:Dim> MultivectorSrc for Odd<T,N> {

    type Scalar = T;
    type Dim = N;
    type Shape = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Odd(Odd::dim(self)) }
    fn elements(&self) -> usize { Odd::elements(self) }
    fn shape(&self) -> N { self.dim_generic() }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_odd(Odd::dim(self), i)
    }

}

impl<T:AllocMultivector<N>, N:Dim> MultivectorSrc for Multivector<T,N> {

    type Scalar = T;
    type Dim = N;
    type Shape = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Full(Multivector::dim(self)) }
    fn elements(&self) -> usize { Multivector::elements(self) }
    fn shape(&self) -> N { self.dim_generic() }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis(Multivector::dim(self), i)
    }

}

macro_rules! impl_src_ref {
    ($Ty:ident<T:$Alloc:ident,N $(, $G:ident)*>) => {
        impl<'a, T:$Alloc<N $(, $G),*>, N:Dim $(, $G:Dim)*> MultivectorSrc for &'a $Ty<T,N $(, $G)*> {

            type Scalar = T;
            type Dim = N;
            type Shape = <$Ty<T,N $(, $G)*> as MultivectorSrc>::Shape;

            fn dim(&self) -> N { MultivectorSrc::dim(*self) }
            fn elements(&self) -> usize { MultivectorSrc::elements(*self) }
            fn subspace(&self) -> Subspace { MultivectorSrc::subspace(*self) }
            fn shape(&self) -> Self::Shape { MultivectorSrc::shape(*self) }

            fn get(&self, i:usize) -> &T { MultivectorSrc::get(*self, i) }
            fn basis(&self, i:usize) -> BasisBlade { MultivectorSrc::basis(*self, i) }

        }
    }
}

impl_src_ref!(Blade<T:AllocBlade,N,G>);
impl_src_ref!(Even<T:AllocEven,N>);
impl_src_ref!(Odd<T:AllocOdd,N>);
impl_src_ref!(Multivector<T:AllocMultivector,N>);

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorDst for Blade<T,N,G> {

    type Uninit = <AllocateBlade<T,N,G> as Storage<T>>::Uninit;

    fn subspace_of((n,g): (N,G)) -> Subspace { Subspace::Blade(n.value(), g.value()) }
    fn uninit((n,g): (N,G)) -> Self::Uninit { AllocateBlade::<T,N,G>::uninit(n,g) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Blade { data: uninit.assume_init() } }

    fn set(&mut self, i:usize, x: Self::Scalar) { self[i] = x }
    fn index_of(basis:BasisBlade, (n,g): (N,G)) -> Option<(usize, bool)> {
        if basis.grade() == g.value() { Some(basis.blade_index_sign(n.value())) } else { None }
    }

}

impl<T:AllocEven<N>, N:Dim> MultivectorDst for Even<T,N> {

    type Uninit = <AllocateEven<T,N> as Storage<T>>::Uninit;

    fn subspace_of(n: N) -> Subspace { Subspace::Even(n.value()) }
    fn uninit(n: N) -> Self::Uninit { AllocateEven::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Even { data: uninit.assume_init() } }

    fn set(&mut self, i:usize, x: Self::Scalar) { self[i] = x }
    fn index_of(basis:BasisBlade, n:N) -> Option<(usize, bool)> {
        if basis.grade()%2 == 0 { Some(basis.even_index_sign(n.value())) } else { None }
    }

}

impl<T:AllocOdd<N>, N:Dim> MultivectorDst for Odd<T,N> {

    type Uninit = <AllocateOdd<T,N> as Storage<T>>::Uninit;

    fn subspace_of(n: N) -> Subspace { Subspace::Odd(n.value()) }
    fn uninit(n: N) -> Self::Uninit { AllocateOdd::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Odd { data: uninit.assume_init() } }

    fn set(&mut self, i:usize, x: Self::Scalar) { self[i] = x }
    fn index_of(basis:BasisBlade, n:N) -> Option<(usize, bool)> {
        if basis.grade()%2 == 0 { Some(basis.odd_index_sign(n.value())) } else { None }
    }

}

impl<T:AllocMultivector<N>, N:Dim> MultivectorDst for Multivector<T,N> {

    type Uninit = <AllocateMultivector<T,N> as Storage<T>>::Uninit;

    fn subspace_of(n: N) -> Subspace { Subspace::Full(n.value()) }
    fn uninit(n: N) -> Self::Uninit { AllocateMultivector::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Multivector { data: uninit.assume_init() } }

    fn set(&mut self, i:usize, x: Self::Scalar) { self[i] = x }
    fn index_of(basis:BasisBlade, n:N) -> Option<(usize, bool)> {
        Some(basis.multivector_index_sign(n.value()))
    }

}

// fn check_dim<B1,B2,B3>(b1: &B1, b2: &B2, shape: B3::Shape) -> usize where
//     B1: MultivectorSrc,
//     B2: MultivectorSrc,
//     B3: MultivectorDst
// {
//     //for convenience
//     let (n1, n2, n3) = (b1.dim().value(), b2.dim().value(), B3::subspace_of(shape).dim());
//
//     //To save further headache with generics, we don't allow multiplying two blades of
//     //different dimension
//     if n1 != n2 {
//         panic!("Cannot multiply two values of different dimensions: {}!={}", n1, n2)
//     }
//
//     if n1 != n3 {
//         panic!("Cannot multiply into a value of different dimension: {}!={}", n1, n3)
//     }
//
//     n1
// }

pub(crate) trait SelectedMul<Rhs, Output:MultivectorDst> {
    fn selected_mul(&self, rhs: &Rhs, shape:Output::Shape) -> Output;
}

macro_rules! impl_selected_mul {

    () => {};

    (
        ($Ty1:ident<T1:$Alloc1:ident,N $(, $G1:ident)*>)
        ($Ty2:ident<T2:$Alloc2:ident,N $(, $G2:ident)*>)
        ($Ty3:ident<T3:$Alloc3:ident,N $(, $G3:ident)*>) @impl
    ) => {

        impl<T1,T2,T3, N:Dim $(, $G1:Dim)* $(, $G2:Dim)* $(, $G3:Dim)*>
            SelectedMul<$Ty2<T2,N $(,$G2)*>, $Ty3<T3,N $(,$G3)*>> for $Ty1<T1,N $(,$G1)*>
        where
            T1: $Alloc1<N $(,$G1)*> + AllRefMul<T2, AllOutput=T3>,
            T2: $Alloc2<N $(,$G2)*>,
            T3: $Alloc3<N $(,$G3)*> + AddGroup,
        {
            fn selected_mul(
                &self, rhs: &$Ty2<T2,N $(,$G2)*>, shape: <$Ty3<T3,N $(,$G3)*> as MultivectorSrc>::Shape
            ) -> $Ty3<T3,N $(,$G3)*> {

                #[cfg(feature = "code_gen")]
                {
                    wedged_macros::gen_mul_optimizations!(
                        self, $Ty1, rhs, $Ty2, shape, $Ty3;
                        core_mul(self, rhs, shape)
                    )
                }

                #[cfg(not(feature = "code_gen"))] { core_mul(self, rhs, shape) }

            }
        }

    };

    (@start) => {
        impl_selected_mul!(
            {(Blade<T1:AllocBlade,N,G1>) (Even<T1:AllocEven,N>) (Odd<T1:AllocOdd,N>) (Multivector<T1:AllocMultivector,N>)}
            {(Blade<T2:AllocBlade,N,G2>) (Even<T2:AllocEven,N>) (Odd<T2:AllocOdd,N>) (Multivector<T2:AllocMultivector,N>)}
            {(Blade<T3:AllocBlade,N,G3>) (Even<T3:AllocEven,N>) (Odd<T3:AllocOdd,N>) (Multivector<T3:AllocMultivector,N>)}
            @start
        );
    };

    ({$($i:tt)*} {$($j:tt)*} {$($k:tt)*} @start) => {
        impl_selected_mul!({$($i)*} [$($i)*] {$($j)*} [$($j)*] {$($k)*} @loop);
    };

    ({$i0:tt $($i:tt)*} [$($I:tt)*] {$j0:tt $($j:tt)*} [$($J:tt)*] {$k0:tt $($k:tt)*} @loop) => {
        impl_selected_mul!({$($i)*} [$($I)*] {$j0 $($j)*} [$($J)*] {$k0 $($k)*} @loop);
        impl_selected_mul!( $i0 $j0 $k0 @impl);
    };

    ({} [$($I:tt)*] {$j0:tt $($j:tt)*} [$($J:tt)*] {$k0:tt $($k:tt)*} @loop) => {
        impl_selected_mul!({$($I)*} [$($I)*] {$($j)*} [$($J)*] {$k0 $($k)*} @loop);
    };

    ({$($i:tt)*} [$($I:tt)*] {} [$($J:tt)*] {$k0:tt $($k:tt)*} @loop) => {
        impl_selected_mul!({$($i)*} [$($I)*] {$($J)*} [$($J)*] {$($k)*} @loop);
    };

    ({$($i:tt)*} [$($I:tt)*] {$($j:tt)*} [$($J:tt)*] {} @loop) => {};

}

// trace_macros!(true);
impl_selected_mul!(@start);
// trace_macros!(false);

// #[inline]
fn core_mul<B1,B2,B3>(b1:B1, b2:B2, shape:B3::Shape) -> B3
where
    B1: MultivectorSrc,
    B2: MultivectorSrc,
    B3: MultivectorDst,
    B1::Scalar: AllRefMul<B2::Scalar, AllOutput=B3::Scalar>,
    // B1::Item: Mul<B2::Item, Output=B3::Scalar>,
    B3::Scalar: AddGroup,
{

    //NOTE: we actually don't have to check the dimensions since the math works out just the same

    //create an unitialized value
    let mut dest = B3::uninit(shape);
    if dest.elements() == 0 { unsafe { return B3::assume_init(dest); } }

    //TODO: optimize a little. We don't always need to initialize beforehand
    for i in 0..dest.elements() {
        dest[i] = MaybeUninit::new(B3::Scalar::zero());
    }

    //do the FOILiest of FOILs
    for i in 0..b1.elements() {
        let basis1 = b1.basis(i);
        for j in 0..b2.elements() {
            let basis2 = b2.basis(j);

            //mul the bases at i and j
            let basis3 = basis1 * basis2;

            //get the index and sign of the result
            if let Some((k, pos)) = B3::index_of(basis3, shape) {
                //multiply the two terms
                let term = b1.get(i).ref_mul(b2.get(j));

                unsafe {
                    if pos {
                        *dest[k].assume_init_mut() += term;
                    } else {
                        *dest[k].assume_init_mut() -= term;
                    }
                }
            }

        }
    }

    unsafe { B3::assume_init(dest) }
}

#[inline]
pub(crate) fn versor_core_mul<B1,B2,B3>(odd:bool, b1:B1, b2:B2, shape:B3::Shape) -> B3
where
    B1: MultivectorSrc,
    B2: MultivectorSrc,
    B3: MultivectorDst,
    B1::Scalar: AllRefMul<B2::Scalar>,
    <B1::Scalar as AllRefMul<B2::Scalar>>::AllOutput: for<'a> Mul<&'a B1::Scalar, Output=B3::Scalar>,
    B3::Scalar: AddGroup,
{

    // check_dim::<_,_,B3>(&b1, &b2, shape);

    //create an unitialized value
    let mut dest = B3::uninit(shape);

    //TODO: optimize a little. We don't always need to initialize beforehand
    for i in 0..dest.elements() {
        dest[i] = MaybeUninit::new(B3::Scalar::zero());
    }

    //do an even more FOILiester FOIL
    for i in 0..b1.elements() {
        let basis1 = b1.basis(i);

        for j in 0..b2.elements() {
            let basis2 = if odd { b2.basis(j).involute() } else { b2.basis(j) };

            for k in 0..b1.elements() {
                let basis3 = b1.basis(k).reverse();

                //mul the bases at i and j and k
                let result_basis = basis1 * basis2 * basis3;

                //get the index and sign of the result
                if let Some((l, pos)) = B3::index_of(result_basis, shape) {
                    //multiply the three terms
                    let term = b1.get(i).ref_mul(b2.get(j)).mul(b1.get(k));

                    unsafe {
                        //TODO: change once assume_init_ref() is stable
                        if pos {
                            *dest[l].as_mut_ptr() += term;
                        } else {
                            *dest[l].as_mut_ptr() -= term;
                        }
                    }
                }

            }

        }
    }

    unsafe { B3::assume_init(dest) }
}


//TODO: when we have specialization, we'll use this to impl optimized varients for each
//statically sized type instead of using if statements in core_mul

///
/// For multiplying two elements of geometric algebra while selecting only certain components
///
/// This can be helpful in situations where it is mathematically known that the product would fit
/// in a particular type, but it is not provable to the compiler.
///
pub trait SelectedGeometricMul<Rhs>: Sized {
    type OutputScalar;
    type N: Dim;

    fn mul_grade_generic<G:Dim>(self, rhs: Rhs, g:G) -> Blade<Self::OutputScalar, Self::N, G>
    where Self::OutputScalar: AllocBlade<Self::N, G>;

    fn mul_dyn_grade(self, rhs: Rhs, g:usize) -> Blade<Self::OutputScalar, Self::N, Dynamic>
    where Self::OutputScalar: AllocBlade<Self::N, Dynamic> {
        self.mul_grade_generic(rhs, Dynamic::new(g))
    }

    fn mul_grade<G:DimName>(self, rhs: Rhs) -> Blade<Self::OutputScalar, Self::N, G>
    where Self::OutputScalar: AllocBlade<Self::N, G> {
        self.mul_grade_generic(rhs, G::name())
    }

    fn mul_even(self, rhs: Rhs) -> Even<Self::OutputScalar, Self::N>
    where Self::OutputScalar: AllocEven<Self::N>;

    fn mul_odd(self, rhs: Rhs) -> Odd<Self::OutputScalar, Self::N>
    where Self::OutputScalar: AllocOdd<Self::N>;

    fn mul_full(self, rhs: Rhs) -> Multivector<Self::OutputScalar, Self::N>
    where Self::OutputScalar: AllocMultivector<Self::N>;

}

// ///
// /// For applying a versor to an object while selecting only certain components
// ///
// /// This can be helpful in situations where it is mathematically known that the product would fit
// /// in a particular type, but it is not provable to the compiler.
// ///
// pub trait SelectedVersorMul<Rhs>: Sized {
//
//     type OutputScalar;
//     type N: Dim;
//
//     fn versor_mul_grade_generic<G:Dim>(self, rhs: Rhs, g:G) -> Blade<Self::OutputScalar, Self::N, G>
//     where Self::OutputScalar: AllocBlade<Self::N, G>;
//
//     fn versor_mul_dyn_grade(self, rhs: Rhs, g:usize) -> Blade<Self::OutputScalar, Self::N, Dynamic>
//     where Self::OutputScalar: AllocBlade<Self::N, Dynamic> {
//         self.versor_mul_grade_generic(rhs, Dynamic::new(g))
//     }
//
//     fn versor_mul_grade<G:DimName>(self, rhs: Rhs) -> Blade<Self::OutputScalar, Self::N, G>
//     where Self::OutputScalar: AllocBlade<Self::N, G> {
//         self.versor_mul_grade_generic(rhs, G::name())
//     }
//
//     fn versor_mul_even(self, rhs: Rhs) -> Even<Self::OutputScalar, Self::N>
//     where Self::OutputScalar: AllocEven<Self::N>;
//
//     fn versor_mul_odd(self, rhs: Rhs) -> Odd<Self::OutputScalar, Self::N>
//     where Self::OutputScalar: AllocOdd<Self::N>;
//
//     fn versor_mul_full(self, rhs: Rhs) -> Multivector<Self::OutputScalar, Self::N>
//     where Self::OutputScalar: AllocMultivector<Self::N>;
//
// }

macro_rules! impl_geometric_mul {

    //end the loop
    () => {};

    //implement one pairing
    (
        @impl
        $(&$a:lifetime)? $Ty1:ident<T:$Alloc1:ident $(, $G1:ident)*> *
        $(&$b:lifetime)? $Ty2:ident<T:$Alloc2:ident $(, $G2:ident)*> =
        $Ty3:ident<T:$Alloc3:ident>;
        $($rest:tt)*
    ) => {

        impl<$($a, )? $($b, )? T1, T2, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
        SelectedGeometricMul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*> where
            T1: $Alloc1<N $(, $G1)*> + AllRefMul<T2, AllOutput=U>,
            T2: $Alloc2<N $(, $G2)*>,
            U: AddGroup,
        {
            type OutputScalar = U;
            type N = N;

            fn mul_grade_generic<G:Dim>(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>, g:G) -> Blade<U, N, G>
            where U: AllocBlade<Self::N, G>
            {
                let shape = (self.dim_generic(), g);
                self.selected_mul(borrow!(rhs, $($b)?), shape)
            }

            fn mul_even(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Even<U, N>
            where U: AllocEven<N>
            {
                let n = self.dim_generic();
                self.selected_mul(borrow!(rhs, $($b)?), n)
            }

            fn mul_odd(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Odd<U, N>
            where U: AllocOdd<N>
            {
                let n = self.dim_generic();
                self.selected_mul(borrow!(rhs, $($b)?), n)
            }

            fn mul_full(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Multivector<U, N>
            where U: AllocMultivector<N>
            {
                let n = self.dim_generic();
                self.selected_mul(borrow!(rhs, $($b)?), n)
            }

        }

        //
        //This is only implemented on values with the same scalar type so as to not conflict with
        //scalar multiplication. Also, most of these output `Multivector` besides the obvious
        //`Even * Even` counterexample. Now yes, even blades times Rotors do result in rotors,
        //but it would mess with the type inference and type checking if we did that even once
        //we have specialization. Instead, users will need to use mul_even() to get that functionality
        //

        impl<$($a, )? $($b, )? T, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
        Mul<$(&$b)? $Ty2<T,N $(,$G2)*>> for $(&$a)? $Ty1<T,N $(,$G1)*> where
            T: $Alloc1<N $(, $G1)*> + $Alloc2<N $(, $G2)*> + AllRefMul<T, AllOutput=U>,
            U: $Alloc3<N> + AddGroup,
        {

            type Output = $Ty3<U,N>;

            fn mul(self, rhs: $(&$b)? $Ty2<T,N $(,$G2)*>) -> $Ty3<U,N> {
                let n = self.dim_generic();
                self.selected_mul(borrow!(rhs, $($b)?), n)
            }

        }

        impl_geometric_mul!($($rest)*);
    };

    //implement over every combination of references
    (
        $Ty1:ident<T:$Alloc1:ident $(, $G1:ident)*> *
        $Ty2:ident<T:$Alloc2:ident $(, $G2:ident)*> =
        $Ty3:ident<T:$Alloc3:ident>;
        $($rest:tt)*
    ) => {
        impl_geometric_mul!(
            @impl     $Ty1<T:$Alloc1 $(, $G1)*> *     $Ty2<T:$Alloc2 $(, $G2)*> = $Ty3<T:$Alloc3>;
            @impl &'a $Ty1<T:$Alloc1 $(, $G1)*> *     $Ty2<T:$Alloc2 $(, $G2)*> = $Ty3<T:$Alloc3>;
            @impl     $Ty1<T:$Alloc1 $(, $G1)*> * &'a $Ty2<T:$Alloc2 $(, $G2)*> = $Ty3<T:$Alloc3>;
            @impl &'a $Ty1<T:$Alloc1 $(, $G1)*> * &'b $Ty2<T:$Alloc2 $(, $G2)*> = $Ty3<T:$Alloc3>;
            $($rest)*
        );
    };

}

impl_geometric_mul!(

    Multivector<T:AllocMultivector> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Multivector<T:AllocMultivector> * Even<T:AllocEven>               = Multivector<T:AllocMultivector>;
    Multivector<T:AllocMultivector> * Odd<T:AllocOdd>                 = Multivector<T:AllocMultivector>;
    Multivector<T:AllocMultivector> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

    Blade<T:AllocBlade,G1> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Blade<T:AllocBlade,G1> * Even<T:AllocEven>               = Multivector<T:AllocMultivector>;
    Blade<T:AllocBlade,G1> * Odd<T:AllocOdd>                 = Multivector<T:AllocMultivector>;
    Blade<T:AllocBlade,G1> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

    Even<T:AllocEven> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Even<T:AllocEven> * Even<T:AllocEven>               = Even<T:AllocEven>;
    Even<T:AllocEven> * Odd<T:AllocOdd>                 = Odd<T:AllocOdd>;
    Even<T:AllocEven> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

    Odd<T:AllocOdd> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Odd<T:AllocOdd> * Even<T:AllocEven>               = Odd<T:AllocOdd>;
    Odd<T:AllocOdd> * Odd<T:AllocOdd>                 = Even<T:AllocEven>;
    Odd<T:AllocOdd> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;


);

// macro_rules! impl_versor_mul {
//
//     () => {};
//
//     (
//         @impl
//         $(&$a:lifetime)? $Ty1:ident<T:$Alloc1:ident $(, $G1:ident)*>
//         $(&$b:lifetime)? $Ty2:ident<T:$Alloc2:ident $(, $G2:ident)*>;
//         $($rest:tt)*
//     ) => {
//         impl<$($a, )? $($b, )? T1, T2, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
//         SelectedVersorMul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*> where
//             T1: $Alloc1<N $(, $G1)*> + AllRefMul<T2, AllOutput=U>,
//             T2: $Alloc2<N $(, $G2)*>,
//             U: for<'c> Mul<&'c T1, Output=U> + AddGroup,
//         {
//             type OutputScalar = U;
//             type N = N;
//
//             fn versor_mul_grade_generic<G:Dim>(
//                 self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>, g:G
//             ) -> Blade<U, N, G>
//             where U: AllocBlade<Self::N, G>
//             {
//                 let shape = (self.dim_generic(), g);
//                 versor_core_mul(self.odd(), self, rhs, shape)
//             }
//
//             fn versor_mul_even(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Even<U, N>
//             where U: AllocEven<N>
//             {
//                 let n = self.dim_generic();
//                 versor_core_mul(self.odd(), self, rhs, n)
//             }
//
//             fn versor_mul_odd(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Odd<U, N>
//             where U: AllocOdd<N>
//             {
//                 let n = self.dim_generic();
//                 versor_core_mul(self.odd(), self, rhs, n)
//             }
//
//             fn versor_mul_full(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Multivector<U, N>
//             where U: AllocMultivector<N>
//             {
//                 let n = self.dim_generic();
//                 versor_core_mul(self.odd(), self, rhs, n)
//             }
//
//         }
//     };
//
//     (
//         $Ty1:ident<T:$Alloc1:ident $(, $G1:ident)*>
//         $Ty2:ident<T:$Alloc2:ident $(, $G2:ident)*>;
//         $($rest:tt)*
//     ) => {
//         impl_versor_mul!(
//             @impl     $Ty1<T:$Alloc1 $(, $G1)*>     $Ty2<T:$Alloc2 $(, $G2)*>;
//             @impl &'a $Ty1<T:$Alloc1 $(, $G1)*>     $Ty2<T:$Alloc2 $(, $G2)*>;
//             @impl     $Ty1<T:$Alloc1 $(, $G1)*> &'a $Ty2<T:$Alloc2 $(, $G2)*> ;
//             @impl &'a $Ty1<T:$Alloc1 $(, $G1)*> &'b $Ty2<T:$Alloc2 $(, $G2)*>;
//             $($rest)*
//         );
//     };
// }
//
// impl_versor_mul!(
//
//     Blade<T:AllocBlade,G1>  Blade<T:AllocBlade,G2>;
//     Blade<T:AllocBlade,G1>  Even<T:AllocEven>;
//     Blade<T:AllocBlade,G1>  Odd<T:AllocOdd>;
//     Blade<T:AllocBlade,G1>  Multivector<T:AllocMultivector>;
//
//     Even<T:AllocEven>  Blade<T:AllocBlade,G2>;
//     Even<T:AllocEven>  Even<T:AllocEven>;
//     Even<T:AllocEven>  Odd<T:AllocOdd>;
//     Even<T:AllocEven>  Multivector<T:AllocMultivector>;
//
//     Odd<T:AllocOdd>  Blade<T:AllocBlade,G2>;
//     Odd<T:AllocOdd>  Even<T:AllocEven>;
//     Odd<T:AllocOdd>  Odd<T:AllocOdd>;
//     Odd<T:AllocOdd>  Multivector<T:AllocMultivector>;
//
//
// );

macro_rules! impl_wedge_dot {
    ($($a:lifetime)?; $($b:lifetime)?) => {
        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G1:Dim,G2:Dim>
            BitXor<$(&$b)? Blade<T2,N,G2>> for $(&$a)? Blade<T1,N,G1>
        where
            T1: AllocBlade<N,G1> + AllRefMul<T2,AllOutput=U>,
            T2: AllocBlade<N,G2>,
            G1: DimAdd<G2>,
            U: AllocBlade<N, DimSum<G1, G2>> + AddGroup,
        {
            type Output = Blade<U,N,DimSum<G1, G2>>;

            // #[inline(always)]
            fn bitxor(self, rhs: $(&$b)? Blade<T2,N,G2>) -> Self::Output {
                let (n, g) = (self.dim_generic(), self.grade_generic().add(rhs.grade_generic()));
                self.selected_mul(borrow!(rhs, $($b)?), (n, g))
            }
        }

        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G1:Dim,G2:Dim>
            Rem<$(&$b)? Blade<T2,N,G2>> for $(&$a)? Blade<T1,N,G1>
        where
            T1: AllocBlade<N,G1> + AllRefMul<T2,AllOutput=U>,
            T2: AllocBlade<N,G2>,
            G1: DimSymSub<G2>,
            U: AllocBlade<N, DimSymDiff<G1, G2>> + AddGroup,
        {
            type Output = Blade<U,N,DimSymDiff<G1,G2>>;

            // #[inline(always)]
            fn rem(self, rhs: $(&$b)? Blade<T2,N,G2>) -> Self::Output {
                let (n, g) = (self.dim_generic(), self.grade_generic().sym_sub(rhs.grade_generic()));
                self.selected_mul(borrow!(rhs, $($b)?), (n, g))
            }
        }
    }
}

impl_wedge_dot!(  ;   );
impl_wedge_dot!('a;   );
impl_wedge_dot!(  ; 'b);
impl_wedge_dot!('a; 'b);

impl<T:AllocEven<N>+AddGroup+Mul<Output=T>+AllRefMul<T,AllOutput=T>+One, N:DimName> One for Even<T,N> {
    // fn is_one(&self) -> bool {
    //     self[0].is_one() &&
    //     self.iter().skip(1).all(|x| x.is_zero())
    // }

    fn set_one(&mut self) {
        self[0].set_one();
        for i in 1..self.elements() { self[i].set_zero() }
    }

    fn one() -> Self {
        Self::from_iterator(once_with(T::one).chain(repeat_with(T::zero)))
    }
}

impl<T:AllocMultivector<N>+AddGroup+Mul<Output=T>+AllRefMul<T,AllOutput=T>+One, N:DimName> One for Multivector<T,N>
{
    // fn is_one(&self) -> bool {
    //     self[0].is_one() &&
    //     self.iter().skip(1).all(|x| x.is_zero())
    // }

    fn set_one(&mut self) {
        self[0].set_one();
        for i in 1..self.elements() { self[i].set_zero() }
    }

    fn one() -> Self {
        Self::from_iterator(once_with(T::one).chain(repeat_with(T::zero)))
    }
}

#[cfg(test)]
mod benches {

    use super::*;
    use test::black_box;
    use test::Bencher;

    //creates a bunch of benches that just apply an operator to two types
    macro_rules! mul_bench {
        ($($fun:ident($x:expr) => $ty1:ident $op:tt $ty2:ident;)*) => {
            $(
                #[bench]
                fn $fun(b: &mut Bencher) {
                    b.iter(
                        || for _ in 0..1000 {
                            black_box(
                                //since we have `black_box()` we just fill each operand with some value
                                black_box($ty1::from_element($x)) $op black_box($ty1::from_element($x))
                            );
                        }
                    )
                }
            )*
        };
    }

    mul_bench!(

        //
        //2D
        //

        wedge_scalar2_scalar2_f32(1.0f32) => Scalar2 ^ Scalar2;
        wedge_scalar2_scalar2_f64(1.0f64) => Scalar2 ^ Scalar2;
        wedge_scalar2_scalar2_i32(1i32) => Scalar2 ^ Scalar2;
        wedge_scalar2_scalar2_i64(1i64) => Scalar2 ^ Scalar2;

        wedge_scalar2_vec2_f32(1.0f32) => Scalar2 ^ Vec2;
        wedge_scalar2_vec2_f64(1.0f64) => Scalar2 ^ Vec2;
        wedge_scalar2_vec2_i32(1i32) => Scalar2 ^ Vec2;
        wedge_scalar2_vec2_i64(1i64) => Scalar2 ^ Vec2;

        wedge_scalar2_bivec2_f32(1.0f32) => Scalar2 ^ BiVec2;
        wedge_scalar2_bivec2_f64(1.0f64) => Scalar2 ^ BiVec2;
        wedge_scalar2_bivec2_i32(1i32) => Scalar2 ^ BiVec2;
        wedge_scalar2_bivec2_i64(1i64) => Scalar2 ^ BiVec2;

        wedge_vec2_vec2_f32(1.0f32) => Vec2 ^ Vec2;
        wedge_vec2_vec2_f64(1.0f64) => Vec2 ^ Vec2;
        wedge_vec2_vec2_i32(1i32) => Vec2 ^ Vec2;
        wedge_vec2_vec2_i64(1i64) => Vec2 ^ Vec2;

        wedge_vec2_bivec2_f32(1.0f32) => Vec2 ^ BiVec2;
        wedge_vec2_bivec2_f64(1.0f64) => Vec2 ^ BiVec2;
        wedge_vec2_bivec2_i32(1i32) => Vec2 ^ BiVec2;
        wedge_vec2_bivec2_i64(1i64) => Vec2 ^ BiVec2;

        wedge_bivec2_bivec2_f32(1.0f32) => BiVec2 ^ BiVec2;
        wedge_bivec2_bivec2_f64(1.0f64) => BiVec2 ^ BiVec2;
        wedge_bivec2_bivec2_i32(1i32) => BiVec2 ^ BiVec2;
        wedge_bivec2_bivec2_i64(1i64) => BiVec2 ^ BiVec2;

        dot_scalar2_scalar2_f32(1.0f32) => Scalar2 % Scalar2;
        dot_scalar2_scalar2_f64(1.0f64) => Scalar2 % Scalar2;
        dot_scalar2_scalar2_i32(1i32) => Scalar2 % Scalar2;
        dot_scalar2_scalar2_i64(1i64) => Scalar2 % Scalar2;

        dot_scalar2_vec2_f32(1.0f32) => Scalar2 % Vec2;
        dot_scalar2_vec2_f64(1.0f64) => Scalar2 % Vec2;
        dot_scalar2_vec2_i32(1i32) => Scalar2 % Vec2;
        dot_scalar2_vec2_i64(1i64) => Scalar2 % Vec2;

        dot_scalar2_bivec2_f32(1.0f32) => Scalar2 % BiVec2;
        dot_scalar2_bivec2_f64(1.0f64) => Scalar2 % BiVec2;
        dot_scalar2_bivec2_i32(1i32) => Scalar2 % BiVec2;
        dot_scalar2_bivec2_i64(1i64) => Scalar2 % BiVec2;

        dot_vec2_vec2_f32(1.0f32) => Vec2 % Vec2;
        dot_vec2_vec2_f64(1.0f64) => Vec2 % Vec2;
        dot_vec2_vec2_i32(1i32) => Vec2 % Vec2;
        dot_vec2_vec2_i64(1i64) => Vec2 % Vec2;

        dot_vec2_bivec2_f32(1.0f32) => Vec2 % BiVec2;
        dot_vec2_bivec2_f64(1.0f64) => Vec2 % BiVec2;
        dot_vec2_bivec2_i32(1i32) => Vec2 % BiVec2;
        dot_vec2_bivec2_i64(1i64) => Vec2 % BiVec2;

        dot_bivec2_bivec2_f32(1.0f32) => BiVec2 % BiVec2;
        dot_bivec2_bivec2_f64(1.0f64) => BiVec2 % BiVec2;
        dot_bivec2_bivec2_i32(1i32) => BiVec2 % BiVec2;
        dot_bivec2_bivec2_i64(1i64) => BiVec2 % BiVec2;

        //
        //3D
        //

        wedge_scalar3_scalar3_f32(1.0f32) => Scalar3 ^ Scalar3;
        wedge_scalar3_scalar3_f64(1.0f64) => Scalar3 ^ Scalar3;
        wedge_scalar3_scalar3_i32(1i32) => Scalar3 ^ Scalar3;
        wedge_scalar3_scalar3_i64(1i64) => Scalar3 ^ Scalar3;

        wedge_scalar3_vec3_f32(1.0f32) => Scalar3 ^ Vec3;
        wedge_scalar3_vec3_f64(1.0f64) => Scalar3 ^ Vec3;
        wedge_scalar3_vec3_i32(1i32) => Scalar3 ^ Vec3;
        wedge_scalar3_vec3_i64(1i64) => Scalar3 ^ Vec3;

        wedge_scalar3_bivec3_f32(1.0f32) => Scalar3 ^ BiVec3;
        wedge_scalar3_bivec3_f64(1.0f64) => Scalar3 ^ BiVec3;
        wedge_scalar3_bivec3_i32(1i32) => Scalar3 ^ BiVec3;
        wedge_scalar3_bivec3_i64(1i64) => Scalar3 ^ BiVec3;

        wedge_scalar3_trivec3_f32(1.0f32) => Scalar3 ^ TriVec3;
        wedge_scalar3_trivec3_f64(1.0f64) => Scalar3 ^ TriVec3;
        wedge_scalar3_trivec3_i32(1i32) => Scalar3 ^ TriVec3;
        wedge_scalar3_trivec3_i64(1i64) => Scalar3 ^ TriVec3;

        wedge_vec3_vec3_f32(1.0f32) => Vec3 ^ Vec3;
        wedge_vec3_vec3_f64(1.0f64) => Vec3 ^ Vec3;
        wedge_vec3_vec3_i32(1i32) => Vec3 ^ Vec3;
        wedge_vec3_vec3_i64(1i64) => Vec3 ^ Vec3;

        wedge_vec3_bivec3_f32(1.0f32) => Vec3 ^ BiVec3;
        wedge_vec3_bivec3_f64(1.0f64) => Vec3 ^ BiVec3;
        wedge_vec3_bivec3_i32(1i32) => Vec3 ^ BiVec3;
        wedge_vec3_bivec3_i64(1i64) => Vec3 ^ BiVec3;

        wedge_vec3_trivec3_f32(1.0f32) => Vec3 ^ TriVec3;
        wedge_vec3_trivec3_f64(1.0f64) => Vec3 ^ TriVec3;
        wedge_vec3_trivec3_i32(1i32) => Vec3 ^ TriVec3;
        wedge_vec3_trivec3_i64(1i64) => Vec3 ^ TriVec3;

        wedge_bivec3_bivec3_f32(1.0f32) => BiVec3 ^ BiVec3;
        wedge_bivec3_bivec3_f64(1.0f64) => BiVec3 ^ BiVec3;
        wedge_bivec3_bivec3_i32(1i32) => BiVec3 ^ BiVec3;
        wedge_bivec3_bivec3_i64(1i64) => BiVec3 ^ BiVec3;

        wedge_bivec3_trivec3_f32(1.0f32) => BiVec3 ^ TriVec3;
        wedge_bivec3_trivec3_f64(1.0f64) => BiVec3 ^ TriVec3;
        wedge_bivec3_trivec3_i32(1i32) => BiVec3 ^ TriVec3;
        wedge_bivec3_trivec3_i64(1i64) => BiVec3 ^ TriVec3;

        wedge_trivec3_trivec3_f32(1.0f32) => TriVec3 ^ TriVec3;
        wedge_trivec3_trivec3_f64(1.0f64) => TriVec3 ^ TriVec3;
        wedge_trivec3_trivec3_i32(1i32) => TriVec3 ^ TriVec3;
        wedge_trivec3_trivec3_i64(1i64) => TriVec3 ^ TriVec3;

        dot_scalar3_scalar3_f32(1.0f32) => Scalar3 % Scalar3;
        dot_scalar3_scalar3_f64(1.0f64) => Scalar3 % Scalar3;
        dot_scalar3_scalar3_i32(1i32) => Scalar3 % Scalar3;
        dot_scalar3_scalar3_i64(1i64) => Scalar3 % Scalar3;

        dot_scalar3_vec3_f32(1.0f32) => Scalar3 % Vec3;
        dot_scalar3_vec3_f64(1.0f64) => Scalar3 % Vec3;
        dot_scalar3_vec3_i32(1i32) => Scalar3 % Vec3;
        dot_scalar3_vec3_i64(1i64) => Scalar3 % Vec3;

        dot_scalar3_bivec3_f32(1.0f32) => Scalar3 % BiVec3;
        dot_scalar3_bivec3_f64(1.0f64) => Scalar3 % BiVec3;
        dot_scalar3_bivec3_i32(1i32) => Scalar3 % BiVec3;
        dot_scalar3_bivec3_i64(1i64) => Scalar3 % BiVec3;

        dot_scalar3_trivec3_f32(1.0f32) => Scalar3 % TriVec3;
        dot_scalar3_trivec3_f64(1.0f64) => Scalar3 % TriVec3;
        dot_scalar3_trivec3_i32(1i32) => Scalar3 % TriVec3;
        dot_scalar3_trivec3_i64(1i64) => Scalar3 % TriVec3;

        dot_vec3_vec3_f32(1.0f32) => Vec3 % Vec3;
        dot_vec3_vec3_f64(1.0f64) => Vec3 % Vec3;
        dot_vec3_vec3_i32(1i32) => Vec3 % Vec3;
        dot_vec3_vec3_i64(1i64) => Vec3 % Vec3;

        dot_vec3_bivec3_f32(1.0f32) => Vec3 % BiVec3;
        dot_vec3_bivec3_f64(1.0f64) => Vec3 % BiVec3;
        dot_vec3_bivec3_i32(1i32) => Vec3 % BiVec3;
        dot_vec3_bivec3_i64(1i64) => Vec3 % BiVec3;

        dot_vec3_trivec3_f32(1.0f32) => Vec3 % TriVec3;
        dot_vec3_trivec3_f64(1.0f64) => Vec3 % TriVec3;
        dot_vec3_trivec3_i32(1i32) => Vec3 % TriVec3;
        dot_vec3_trivec3_i64(1i64) => Vec3 % TriVec3;

        dot_bivec3_bivec3_f32(1.0f32) => BiVec3 % BiVec3;
        dot_bivec3_bivec3_f64(1.0f64) => BiVec3 % BiVec3;
        dot_bivec3_bivec3_i32(1i32) => BiVec3 % BiVec3;
        dot_bivec3_bivec3_i64(1i64) => BiVec3 % BiVec3;

        dot_bivec3_trivec3_f32(1.0f32) => BiVec3 % TriVec3;
        dot_bivec3_trivec3_f64(1.0f64) => BiVec3 % TriVec3;
        dot_bivec3_trivec3_i32(1i32) => BiVec3 % TriVec3;
        dot_bivec3_trivec3_i64(1i64) => BiVec3 % TriVec3;

        dot_trivec3_trivec3_f32(1.0f32) => TriVec3 % TriVec3;
        dot_trivec3_trivec3_f64(1.0f64) => TriVec3 % TriVec3;
        dot_trivec3_trivec3_i32(1i32) => TriVec3 % TriVec3;
        dot_trivec3_trivec3_i64(1i64) => TriVec3 % TriVec3;

        //
        //the rest
        //

        wedge_vec4_f32(1.0f32) => Vec4 ^ Vec4;
        wedge_vec4_f64(1.0f64) => Vec4 ^ Vec4;
        wedge_vec4_i32(1i32) => Vec4 ^ Vec4;
        wedge_vec4_i64(1i64) => Vec4 ^ Vec4;

        wedge_vec5_f32(1.0f32) => Vec5 ^ Vec5;
        wedge_vec5_f64(1.0f64) => Vec5 ^ Vec5;
        wedge_vec5_i32(1i32) => Vec5 ^ Vec5;
        wedge_vec5_i64(1i64) => Vec5 ^ Vec5;

        wedge_vec6_f32(1.0f32) => Vec6 ^ Vec6;
        wedge_vec6_f64(1.0f64) => Vec6 ^ Vec6;
        wedge_vec6_i32(1i32) => Vec6 ^ Vec6;
        wedge_vec6_i64(1i64) => Vec6 ^ Vec6;

        wedge_bivec6_f32(1.0f32) => BiVec6 ^ BiVec6;
        wedge_bivec6_f64(1.0f64) => BiVec6 ^ BiVec6;
        wedge_bivec6_i32(1i32) => BiVec6 ^ BiVec6;
        wedge_bivec6_i64(1i64) => BiVec6 ^ BiVec6;

        dot_vec4_f32(1.0f32) => Vec4 % Vec4;
        dot_vec4_f64(1.0f64) => Vec4 % Vec4;
        dot_vec4_i32(1i32) => Vec4 % Vec4;
        dot_vec4_i64(1i64) => Vec4 % Vec4;

        dot_vec5_f32(1.0f32) => Vec5 % Vec5;
        dot_vec5_f64(1.0f64) => Vec5 % Vec5;
        dot_vec5_i32(1i32) => Vec5 % Vec5;
        dot_vec5_i64(1i64) => Vec5 % Vec5;

        dot_vec6_f32(1.0f32) => Vec6 % Vec6;
        dot_vec6_f64(1.0f64) => Vec6 % Vec6;
        dot_vec6_i32(1i32) => Vec6 % Vec6;
        dot_vec6_i64(1i64) => Vec6 % Vec6;

        dot_bivec6_f32(1.0f32) => BiVec6 % BiVec6;
        dot_bivec6_f64(1.0f64) => BiVec6 % BiVec6;
        dot_bivec6_i32(1i32) => BiVec6 % BiVec6;
        dot_bivec6_i64(1i64) => BiVec6 % BiVec6;
    );


}

#[cfg(test)]
#[allow(non_upper_case_globals)]
mod tests {

    use super::*;

    const e1: Vec3<i32> = Vec3::new(1, 0, 0);
    const e2: Vec3<i32> = Vec3::new(0, 1, 0);
    const e3: Vec3<i32> = Vec3::new(0, 0, 1);

    const e23: BiVec3<i32> = BiVec3::new(1, 0, 0);
    const e31: BiVec3<i32> = BiVec3::new(0, 1, 0);
    const e12: BiVec3<i32> = BiVec3::new(0, 0, 1);

    const e123: TriVec3<i32> = TriVec3::new(1);

    macro_rules! test_mul {
        ($b1:ident $op:tt $b2:ident == $b3:expr; $commutative:literal) => {

            assert_eq!( $b1 $op $b2,  $b3);
            assert_eq!(-$b1 $op $b2, -$b3);
            assert_eq!( $b1 $op-$b2, -$b3);
            assert_eq!(-$b1 $op-$b2,  $b3);

            if $commutative {
                assert_eq!( $b2 $op $b1,  $b3);
                assert_eq!(-$b2 $op $b1, -$b3);
                assert_eq!( $b2 $op-$b1, -$b3);
                assert_eq!(-$b2 $op-$b1,  $b3);
            } else {
                assert_eq!( $b2 $op $b1, -$b3);
                assert_eq!(-$b2 $op $b1,  $b3);
                assert_eq!( $b2 $op-$b1,  $b3);
                assert_eq!(-$b2 $op-$b1, -$b3);
            }

        }
    }

    //makes sure that the multiplication agrees with BasisBlade
    #[test]
    fn basis() {

        use rayon::prelude::*;

        let count = (1 as i32) << 8;

        (0..count).into_par_iter().for_each(
            |bits1| {
                let b1 = BasisBlade::from_bits(bits1);
                let (n1, g1) = (b1.dim(), b1.grade());

                (0..count).into_par_iter().for_each(
                    |bits2| {
                        let b2 = BasisBlade::from_bits(bits2);
                        let (n2, g2) = (b2.dim(), b2.grade());

                        //multiply the two basis as BasisBlade's
                        let b3 = b1*b2;
                        let g3 = b3.grade();

                        //
                        //convert the BasisBlade's into BladeD's
                        //

                        let n = n1.max(n2);
                        let sign = |pos| if pos { 1i32 } else { -1i32 };

                        let (i, pos1) = b1.blade_index_sign(n);
                        let (j, pos2) = b2.blade_index_sign(n);
                        let (k, pos3) = b3.blade_index_sign(n);

                        let x1 = sign(pos1) * BladeD::basis(n, g1, i);
                        let x2 = sign(pos2) * BladeD::basis(n, g2, j);
                        let x3 = sign(pos3) * BladeD::basis(n, g3, k);

                        //
                        //Test for consistency
                        //

                        // let left = core_mul::<_,_,BladeD<_>>(
                        //     x1.clone(), x2.clone(), (Dynamic::new(n), Dynamic::new(g3))
                        // );

                        let left: BladeD<_> = x1.selected_mul(&x2.clone(), (Dynamic::new(n), Dynamic::new(g3)));

                        let right = x3;

                        // println!("{}*{} = {}, {}", x1, x2, left, right);
                        assert_eq!(left, right);
                    }
                )

            }
        );

    }

    #[test]
    fn basis3d() {

        let e = Scalar3::new(1);

        let zero = Scalar3::new(0);
        let zerov = Vec3::zero();
        let zerob = BiVec3::zero();
        let zeroq = Blade::<_,U3,U4>::zero();

        test_mul!(e^e == e; true);
        test_mul!(e^e1 == e1; true);
        test_mul!(e^e2 == e2; true);
        test_mul!(e^e3 == e3; true);
        test_mul!(e^e23 == e23; true);
        test_mul!(e^e31 == e31; true);
        test_mul!(e^e23 == e23; true);
        test_mul!(e^e123 == e123; true);

        test_mul!(e1^e1 == zerob; false);
        test_mul!(e2^e2 == zerob; false);
        test_mul!(e3^e3 == zerob; false);

        test_mul!(e23^e23 == zeroq; false);
        test_mul!(e31^e31 == zeroq; false);
        test_mul!(e12^e12 == zeroq; false);

        test_mul!(e1^e2 == e12; false);
        test_mul!(e3^e1 == e31; false);
        test_mul!(e2^e3 == e23; false);

        test_mul!(e1^e23 == e123; true);
        test_mul!(e2^e31 == e123; true);
        test_mul!(e3^e12 == e123; true);

        test_mul!(e%e    == e;    true);
        test_mul!(e%e1   == e1;   true);
        test_mul!(e%e2   == e2;   true);
        test_mul!(e%e3   == e3;   true);
        test_mul!(e%e23  == e23;  true);
        test_mul!(e%e31  == e31;  true);
        test_mul!(e%e12  == e12;  true);
        test_mul!(e%e123 == e123; true);

        test_mul!(e1%e1 == e; true);
        test_mul!(e1%e2 == zero; true);
        test_mul!(e1%e3 == zero; true);
        test_mul!(e2%e2 == e; true);
        test_mul!(e2%e3 == zero; true);
        test_mul!(e3%e3 == e; true);

        test_mul!(e1%e23 == zerov; false);
        test_mul!(e1%e31 == -e3; false);
        test_mul!(e1%e12 == e2; false);
        test_mul!(e2%e23 == e3; false);
        test_mul!(e2%e31 == zerov; false);
        test_mul!(e2%e12 == -e1; false);
        test_mul!(e3%e23 == -e2; false);
        test_mul!(e3%e31 == e1; false);
        test_mul!(e3%e12 == zerov; false);

        test_mul!(e1%e123  == e23; true);
        test_mul!(e2%e123  == e31; true);
        test_mul!(e3%e123  == e12; true);
        test_mul!(e23%e123 == -e1; true);
        test_mul!(e31%e123 == -e2; true);
        test_mul!(e12%e123 == -e3; true);

    }

    #[test]
    fn zero_from_degenerate() {

        //a degenerate blade
        let zeroq = Blade::<i32,U3,U4>::zero();

        let zerov = Vec3::zero();
        let zerob = BiVec3::zero();
        let zerot = TriVec3::zero();

        assert_eq!(e1%zeroq, zerot);
        assert_eq!(e2%zeroq, zerot);
        assert_eq!(e3%zeroq, zerot);

        assert_eq!(e23%zeroq, zerob);
        assert_eq!(e31%zeroq, zerob);
        assert_eq!(e12%zeroq, zerob);

        assert_eq!(e123%zeroq, zerov);


    }

}
