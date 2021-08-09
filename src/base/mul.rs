
use super::*;

pub trait RefMul<Rhs:?Sized> {
    type Output;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b Rhs) -> Self::Output;
}

impl<T1:?Sized,T2:?Sized,U> RefMul<T2> for T1 where for<'a,'b> &'a T1: Mul<&'b T2,Output=U> {
    type Output = U;
    fn ref_mul<'a,'b>(&'a self, rhs:&'b T2) -> U { self * rhs }
}

#[derive(Clone, Copy, Debug)]
enum Subspace {
    Blade(usize, usize),
    Even(usize),
    Full(usize)
}

impl Subspace {
    fn dim(&self) -> usize {
        match self {
            Self::Blade(n,_) => *n,
            Self::Even(n) => *n,
            Self::Full(n) => *n
        }
    }
}

trait MultivectorSrc:IntoIterator {

    type Scalar;
    type Dim: Dim;

    fn dim(&self) -> Self::Dim;
    fn elements(&self) -> usize;
    fn subspace(&self) -> Subspace;

    fn get(&self, i:usize) -> &Self::Scalar;
    fn basis(&self, i:usize) -> BasisBlade;
}

trait MultivectorDst: MultivectorSrc {

    type Shape: Copy;
    type Uninit: UninitStorage<Self::Scalar>;

    fn subspace_of(shape: Self::Shape) -> Subspace;

    fn uninit(shape: Self::Shape) -> Self::Uninit;
    unsafe fn assume_init(uninit:Self::Uninit) -> Self;

    fn index_of(basis:BasisBlade, shape:Self::Shape) -> Option<(usize, bool)>;

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorSrc for Blade<T,N,G> {

    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Blade(Blade::dim(self), self.grade()) }
    fn elements(&self) -> usize { Blade::elements(self) }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_blade(Blade::dim(self), self.grade(), i)
    }

}

impl<T:AllocRotor<N>, N:Dim> MultivectorSrc for Rotor<T,N> {

    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Even(Rotor::dim(self)) }
    fn elements(&self) -> usize { Rotor::elements(self) }

    fn get(&self, i:usize) -> &T { &self[i] }
    fn basis(&self, i:usize) -> BasisBlade {
        BasisBlade::basis_rotor(Rotor::dim(self), i)
    }

}

impl<T:AllocMultivector<N>, N:Dim> MultivectorSrc for Multivector<T,N> {

    type Scalar = T;
    type Dim = N;

    fn dim(&self) -> N { self.dim_generic() }
    fn subspace(&self) -> Subspace { Subspace::Full(Multivector::dim(self)) }
    fn elements(&self) -> usize { Multivector::elements(self) }

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

            fn dim(&self) -> N { MultivectorSrc::dim(*self) }
            fn elements(&self) -> usize { MultivectorSrc::elements(*self) }
            fn subspace(&self) -> Subspace { MultivectorSrc::subspace(*self) }

            fn get(&self, i:usize) -> &T { MultivectorSrc::get(*self, i) }
            fn basis(&self, i:usize) -> BasisBlade { MultivectorSrc::basis(*self, i) }

        }
    }
}

impl_src_ref!(Blade<T:AllocBlade,N,G>);
impl_src_ref!(Rotor<T:AllocRotor,N>);
impl_src_ref!(Multivector<T:AllocMultivector,N>);

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> MultivectorDst for Blade<T,N,G> {

    type Shape = (N, G);
    type Uninit = <AllocateBlade<T,N,G> as Storage<T>>::Uninit;

    fn subspace_of((n,g): (N,G)) -> Subspace { Subspace::Blade(n.value(), g.value()) }
    fn uninit((n,g): (N,G)) -> Self::Uninit { AllocateBlade::<T,N,G>::uninit(n,g) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Blade { data: uninit.assume_init() } }

    fn index_of(basis:BasisBlade, (n,g): (N,G)) -> Option<(usize, bool)> {
        if basis.grade() == g.value() { Some(basis.blade_index_sign(n.value())) } else { None }
    }

}

impl<T:AllocRotor<N>, N:Dim> MultivectorDst for Rotor<T,N> {

    type Shape = N;
    type Uninit = <AllocateRotor<T,N> as Storage<T>>::Uninit;

    fn subspace_of(n: N) -> Subspace { Subspace::Even(n.value()) }
    fn uninit(n: N) -> Self::Uninit { AllocateRotor::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Rotor { data: uninit.assume_init() } }

    fn index_of(basis:BasisBlade, n:N) -> Option<(usize, bool)> {
        if basis.grade()%2 == 0 { Some(basis.rotor_index_sign(n.value())) } else { None }
    }

}

impl<T:AllocMultivector<N>, N:Dim> MultivectorDst for Multivector<T,N> {

    type Shape = N;
    type Uninit = <AllocateMultivector<T,N> as Storage<T>>::Uninit;

    fn subspace_of(n: N) -> Subspace { Subspace::Full(n.value()) }
    fn uninit(n: N) -> Self::Uninit { AllocateMultivector::<T,N>::uninit(n) }
    unsafe fn assume_init(uninit: Self::Uninit) -> Self { Multivector { data: uninit.assume_init() } }

    fn index_of(basis:BasisBlade, n:N) -> Option<(usize, bool)> {
        Some(basis.multivector_index_sign(n.value()))
    }

}

fn mul_selected<B1,B2,B3,N:Dim>(b1:B1, b2:B2, shape:B3::Shape) -> B3
where
    B1: MultivectorSrc<Dim=N>,
    B2: MultivectorSrc<Dim=N>,
    B3: MultivectorDst<Dim=N>,
    B1::Scalar: RefMul<B2::Scalar, Output=B3::Scalar>,
    B1::Item: Mul<B2::Item, Output=B3::Scalar>,
    B3::Scalar: ClosedAdd + ClosedSub + Neg<Output=B3::Scalar> + Zero,
{

    let (n1, n2, n3) = (b1.dim().value(), b2.dim().value(), B3::subspace_of(shape).dim());

    //To save further headache with generics, we don't allow multiplying two blades of
    //different dimension
    if n1 != n2 {
        panic!("Cannot multiply two values of different dimensions: {}!={}", n1, n2)
    }

    if n1 != n3 {
        panic!("Cannot multiply into a value of different dimension: {}!={}", n1, n3)
    }

    let n = n1;

    //
    //The *slow* method
    //

    //create an unitialized value
    let mut dest = B3::uninit(shape);

    //special cases where we can apply certain optimization
    use Subspace::*;
    match (b1.subspace(), b2.subspace(), B3::subspace_of(shape)) {

        //the scalar product of two blades
        (Blade(_,g), Blade(_,g2), Blade(_,0)) if g==g2 => {

            let dot = b1.into_iter().zip(b2).map(|(t1,t2)| t1*t2).fold(B3::Scalar::zero(), |d,t| d+t);

            dest[0] = MaybeUninit::new(
                //do `(-1)^(g*(g-1)/2) * dot`
                if (g&0b10) == 0 { dot } else { -dot }
            );

            return unsafe { B3::assume_init(dest) };

        },

        //wedging two blades into the psuedoscalar
        (Blade(_,g1), Blade(_,g2), Blade(_,n2)) if n==n2 && g1+g2==n2 => {

            if g1!=g2 {
                let dot = b1.into_iter().zip(b2).map(|(t1,t2)| t1*t2).fold(B3::Scalar::zero(), |d,t| d+t);
                let neg = ((g1&0b10) != 0) ^ (g1>g2 && ((n&0b10) != 0));

                dest[0] = MaybeUninit::new( if neg { -dot } else { dot } );
                return unsafe { B3::assume_init(dest) };
            } else {

            }

        },

        // (Blade(3,1), Blade(3,1), Blade(3,2)) => {
        //     dest[0] = MaybeUninit::new(b1.get(1).ref_mul(b2.get(2)) - b1.get(2).ref_mul(b2.get(1)));
        //     dest[1] = MaybeUninit::new(b1.get(2).ref_mul(b2.get(0)) - b1.get(0).ref_mul(b2.get(2)));
        //     dest[2] = MaybeUninit::new(b1.get(0).ref_mul(b2.get(1)) - b1.get(1).ref_mul(b2.get(0)));
        //     return unsafe { B3::assume_init(dest) };
        // },
        _ => (),
    }

    //TODO: optimize a little. We don't always need to initialize beforehand
    for i in 0..dest.elements() {
        dest[i] = MaybeUninit::new(B3::Scalar::zero());
    }

    //this is irrelevant now
    // let mut written_to = vec![true; dest.elements()];


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

                //write or add the result to the destination blade
                // if written_to[k] {
                    unsafe {
                        //TODO: change once assume_init_ref() is stable
                        if pos {
                            *dest[k].as_mut_ptr() += term;
                        } else {
                            *dest[k].as_mut_ptr() -= term;
                        }
                    }
                // } else {
                    // dest[k] = MaybeUninit::new(if pos {term} else {-term});
                    // written_to[k] = true;
                // }
            }

        }
    }

    unsafe { B3::assume_init(dest) }
}

//TODO: when we have specialization, we'll use this to impl optimized varients for each
//statically sized type instead of using if statements in mul_selected

pub trait GeometricMul<Rhs> {
    type OutputScalar;
    type N: Dim;

    fn mul_grade_generic<G:Dim>(self, rhs: Rhs, g:G) -> Blade<Self::OutputScalar, Self::N, G>
    where Self::OutputScalar: AllocBlade<Self::N, G>;

    fn mul_dyn_grade(self, rhs: Rhs, g:usize) -> Blade<Self::OutputScalar, Self::N, Dynamic>
    where Self::OutputScalar: AllocBlade<Self::N, Dynamic>;

    fn mul_grade<G:DimName>(self, rhs: Rhs) -> Blade<Self::OutputScalar, Self::N, G>
    where Self::OutputScalar: AllocBlade<Self::N, G>;

    fn mul_even(self, rhs: Rhs) -> Rotor<Self::OutputScalar, Self::N>
    where Self::OutputScalar: AllocRotor<Self::N>;

    fn mul_full(self, rhs: Rhs) -> Multivector<Self::OutputScalar, Self::N>
    where Self::OutputScalar: AllocMultivector<Self::N>;

}

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
        GeometricMul<$(&$b)? $Ty2<T2,N $(,$G2)*>> for $(&$a)? $Ty1<T1,N $(,$G1)*> where
            T1: $Alloc1<N $(, $G1)*> + RefMul<T2, Output=U>,
            T2: $Alloc2<N $(, $G2)*>,
            U: ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
            $(&$a)? T1: Mul<$(&$b)? T2, Output=U>
        {
            type OutputScalar = U;
            type N = N;

            fn mul_grade_generic<G:Dim>(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>, g:G) -> Blade<U, N, G>
            where U: AllocBlade<Self::N, G>
            {
                let shape = (self.dim_generic(), g);
                mul_selected(self, rhs, shape)
            }

            fn mul_dyn_grade(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>, g:usize) -> Blade<U, N, Dynamic>
            where U: AllocBlade<Self::N, Dynamic>
            {
                self.mul_grade_generic(rhs, Dynamic::new(g))
            }

            fn mul_grade<G:DimName>(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Blade<U, N, G>
            where U: AllocBlade<Self::N, G>
            {
                self.mul_grade_generic(rhs, G::name())
            }

            fn mul_even(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Rotor<U, N>
            where U: AllocRotor<N>
            {
                let n = self.dim_generic();
                mul_selected(self, rhs, n)
            }

            fn mul_full(self, rhs: $(&$b)? $Ty2<T2,N $(,$G2)*>) -> Multivector<U, N>
            where U: AllocMultivector<N>
            {
                let n = self.dim_generic();
                mul_selected(self, rhs, n)
            }

        }

        //
        //This is only implemented on values with the same scalar type so as to not conflict with
        //scalar multiplication. Also, most of these output `Multivector` besides the obvious
        //`Rotor * Rotor` counterexample. Now yes, even blades times Rotors do result in rotors,
        //but it would mess with the type inference and type checking if we did that even once
        //we have specialization. Instead, users will need to use mul_even() to get that functionality
        //

        impl<$($a, )? $($b, )? T, U, N:Dim $(, $G1:Dim)* $(, $G2:Dim)*>
        Mul<$(&$b)? $Ty2<T,N $(,$G2)*>> for $(&$a)? $Ty1<T,N $(,$G1)*> where
            T: $Alloc1<N $(, $G1)*> + $Alloc2<N $(, $G2)*> + RefMul<T, Output=U>,
            U: $Alloc3<N> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
            $(&$a)? T: Mul<$(&$b)? T, Output=U>
        {

            type Output = $Ty3<U,N>;

            fn mul(self, rhs: $(&$b)? $Ty2<T,N $(,$G2)*>) -> $Ty3<U,N> {
                let n = self.dim_generic();
                mul_selected(self, rhs, n)
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

    Blade<T:AllocBlade,G1> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Blade<T:AllocBlade,G1> * Rotor<T:AllocRotor>             = Multivector<T:AllocMultivector>;
    Blade<T:AllocBlade,G1> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

    Rotor<T:AllocRotor> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Rotor<T:AllocRotor> * Rotor<T:AllocRotor>             = Rotor<T:AllocRotor>;
    Rotor<T:AllocRotor> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

    Multivector<T:AllocMultivector> * Blade<T:AllocBlade,G2>          = Multivector<T:AllocMultivector>;
    Multivector<T:AllocMultivector> * Rotor<T:AllocRotor>             = Multivector<T:AllocMultivector>;
    Multivector<T:AllocMultivector> * Multivector<T:AllocMultivector> = Multivector<T:AllocMultivector>;

);

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> BitXor<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + Mul<T2,Output=U> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G1: DimAdd<G2>,
    U: AllocBlade<N, DimSum<G1, G2>> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
{
    type Output = Blade<U,N,DimSum<G1, G2>>;
    fn bitxor(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let (n, g) = (self.dim_generic(), self.grade_generic().add(rhs.grade_generic()));
        mul_selected(self, rhs, (n, g))
    }
}

impl<T1,T2,U,N:Dim,G1:Dim,G2:Dim> Rem<Blade<T2,N,G2>> for Blade<T1,N,G1> where
    T1: AllocBlade<N,G1> + Mul<T2,Output=U> + RefMul<T2,Output=U>,
    T2: AllocBlade<N,G2>,
    G2: DimSub<G1>,
    U: AllocBlade<N, DimDiff<G2, G1>> + ClosedAdd + ClosedSub + Neg<Output=U> + Zero,
{
    type Output = Blade<U,N,DimDiff<G2, G1>>;
    fn rem(self, rhs: Blade<T2,N,G2>) -> Self::Output {
        let (n, g) = (self.dim_generic(), rhs.grade_generic().sub(self.grade_generic()));
        mul_selected(self, rhs, (n, g))
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
                        || black_box(
                            //since we have `black_box()` we just fill each operand with some value
                            black_box($ty1::from_element($x)) $op black_box($ty1::from_element($x))
                        )
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

        use crate::basis_blade::*;
        use rayon::prelude::*;

        let count = (1 as Bits) << 8;

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
                        let mut x1 = BladeD::from_element(n, g1, 0);
                        let mut x2 = BladeD::from_element(n, g2, 0);
                        let mut x3 = BladeD::from_element(n, g3, 0);

                        let (i, pos1) = b1.blade_index_sign(n);
                        let (j, pos2) = b2.blade_index_sign(n);
                        let (k, pos3) = b3.blade_index_sign(n);

                        x1[i] = if pos1 { 1 } else { -1 };
                        x2[j] = if pos2 { 1 } else { -1 };
                        x3[k] = if pos3 { 1 } else { -1 };

                        //
                        //Test for consistency
                        //

                        let left = mul_selected::<_,_,BladeD<_>,Dynamic>(
                            x1.clone(), x2.clone(), (Dynamic::new(n), Dynamic::new(g3))
                        );

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

        assert_eq!(e%e, e);
        assert_eq!(e%e1, e1);
        assert_eq!(e%e2, e2);
        assert_eq!(e%e3, e3);
        assert_eq!(e%e23, e23);
        assert_eq!(e%e31, e31);
        assert_eq!(e%e12, e12);
        assert_eq!(e%e123, e123);

        test_mul!(e1%e1 == e; true);
        test_mul!(e1%e2 == zero; true);
        test_mul!(e1%e3 == zero; true);
        test_mul!(e2%e2 == e; true);
        test_mul!(e2%e3 == zero; true);
        test_mul!(e3%e3 == e; true);

        assert_eq!(e1%e23, zerov);
        assert_eq!(e1%e31, -e3);
        assert_eq!(e1%e12, e2);
        assert_eq!(e2%e23, e3);
        assert_eq!(e2%e31, zerov);
        assert_eq!(e2%e12, -e1);
        assert_eq!(e3%e23, -e2);
        assert_eq!(e3%e31, e1);
        assert_eq!(e3%e12, zerov);

        assert_eq!(e1%e123, e23);
        assert_eq!(e2%e123, e31);
        assert_eq!(e3%e123, e12);
        assert_eq!(e23%e123, -e1);
        assert_eq!(e31%e123, -e2);
        assert_eq!(e12%e123, -e3);

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
