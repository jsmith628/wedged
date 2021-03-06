
use super::*;

//
//Index Ops
//

macro_rules! impl_index {
    ($Ty:ident<T:$Alloc:ident, $($N:ident),*>) => {

        //Currently, we just to indexing wrt `usize`. There may be additions in the future, but
        //unlike with Matrices or slices, ranges don't really make much sense, and while indexing wrt
        //basis blades _may_ make sense, it's slow *and* we have to deal with a potential minus sign.

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> Index<usize> for $Ty<T,$($N),*> {
            type Output = T;
            fn index(&self, i: usize) -> &T { &self.data[i] }
        }

        impl<T:$Alloc<$($N),*>, $($N:Dim),*> IndexMut<usize> for $Ty<T,$($N),*> {
            fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
        }

    }
}

impl_index!(Blade<T:AllocBlade, N, G>);
impl_index!(Even<T:AllocEven, N>);
impl_index!(Odd<T:AllocOdd, N>);
impl_index!(Multivector<T:AllocMultivector, N>);

//
//Fn calls
//

//This is probably stupid and will not get used... but it's cool anyway!
#[cfg(feature = "fn_traits")]
mod fn_impl {

    use super::*;

    macro_rules! impl_fn {
        ($Ty:ident<T:$Alloc:ident, $($N:ident),*>) => {

            impl<T:$Alloc<$($N),*>, U:$Alloc<$($N),*>, $($N:Dim,)* Args> FnOnce<Args> for $Ty<T,$($N),*> where
                T: FnOnce<Args, Output=U>,
                Args: Clone
            {
                type Output = $Ty<U,$($N),*>;
                extern "rust-call" fn call_once(self, args: Args) -> $Ty<U,$($N),*> {
                    #[allow(non_snake_case, unused_parens)]
                    let ($($N),*) = self.shape();
                    $Ty::from_iter_generic(
                        $($N,)* self.into_iter().map(|f| f.call_once(args.clone()))
                    )
                }
            }

            impl<T:$Alloc<$($N),*>, U:$Alloc<$($N),*>, $($N:Dim,)* Args> FnMut<Args> for $Ty<T,$($N),*> where
                T: FnMut<Args, Output=U>,
                Args: Clone
            {
                extern "rust-call" fn call_mut(&mut self, args: Args) -> $Ty<U,$($N),*> {
                    #[allow(non_snake_case, unused_parens)]
                    let ($($N),*) = self.shape();
                    $Ty::from_iter_generic(
                        $($N,)* self.iter_mut().map(|f| f.call_mut(args.clone()))
                    )
                }
            }

            impl<T:$Alloc<$($N),*>, U:$Alloc<$($N),*>, $($N:Dim,)* Args> Fn<Args> for $Ty<T,$($N),*> where
                T: Fn<Args, Output=U>,
                Args: Clone
            {
                extern "rust-call" fn call(&self, args: Args) -> $Ty<U,$($N),*> {
                    #[allow(non_snake_case, unused_parens)]
                    let ($($N),*) = self.shape();
                    $Ty::from_iter_generic(
                        $($N,)* self.iter().map(|f| f.call(args.clone()))
                    )
                }
            }

        }
    }

    impl_fn!(Blade<T:AllocBlade, N, G>);
    impl_fn!(Even<T:AllocEven, N>);
    impl_fn!(Odd<T:AllocOdd, N>);
    impl_fn!(Multivector<T:AllocMultivector, N>);

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn circle_path() {

            //have to use a dyn type because every function (including closures) is a seperate type
            type F<'a> = &'a dyn Fn(f64) -> f64;

            let circle = Vec2::<F>::new(&f64::cos, &f64::sin);

            for i in 0..360 {
                let t = i as f64 * 2.0*std::f64::consts::PI / 360.0;
                assert_eq!(circle(t), Vec2::new(t.cos(), t.sin()))
            }

        }

    }

}

//
//Addition and Subtraction
//

//we do this as a macro to make it easier to do with both references and values
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
        if d1!=d2 { panic!("Cannot add values of different dimension: {}!={}", d1.value(), d2.value()); }

    };
}

//to make the code shorter
macro_rules! uninit {
    ($self:ident, $ty:ty) => {
        <DefaultAllocator as Alloc<$ty>>::uninit($self.shape())
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

macro_rules! impl_binops {

    //implements operation with optional references
    (
        impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident
        with $Op2:ident.$op2:ident();
        $($a:lifetime)?; $($b:lifetime)?
    ) => {

        impl<$($a,)? $($b,)? T1,T2,U,$($N:Dim),*> $Op<$(&$b)? $Ty<T2,$($N),*>> for $(&$a)? $Ty<T1,$($N),*>
        where
            T1: $Alloc<$($N),*>,
            T2: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            T1: $Op2<$($a, )? $(&$b)? T2, Output=U>
        {

            type Output = $Ty<U,$($N),*>;

            fn $op(self, rhs: $(&$b)? $Ty<T2,$($N),*>) -> $Ty<U,$($N),*> {

                check!(self, rhs, $Ty);

                let mut dest = uninit!(self, Self::Output);
                for ((t1, t2), u) in self.into_iter().zip(rhs).zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op2(t2));
                }

                $Ty { data: unsafe { dest.assume_init() } }

            }

        }

    };

    //do every combination of reference and value
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Ref:ident.$ref:ident()) => {
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Op.$op()  ;   ;   );
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Ref.$ref(); 'a;   );
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Op.$op()  ;   ; 'b);
        impl_binops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Ref.$ref(); 'a; 'b);
    };

    //impl for Add, AddAssign, Sub, and SubAssign
    (impl<T:$Alloc:ident,$($N:ident),*> for $Ty:ident) => {
        impl_binops!(impl<T:$Alloc,$($N),*> Add.add() for $Ty with RefAdd.ref_add());
        impl_binops!(impl<T:$Alloc,$($N),*> Sub.sub() for $Ty with RefSub.ref_sub());
        impl_assign_binops!(impl<T:$Alloc,$($N),*> AddAssign.add_assign() for $Ty);
        impl_assign_binops!(impl<T:$Alloc,$($N),*> SubAssign.sub_assign() for $Ty);
    };

}

impl_binops!(impl<T:AllocBlade,N,G> for Blade);
impl_binops!(impl<T:AllocEven,N> for Even);
impl_binops!(impl<T:AllocOdd,N> for Odd);
impl_binops!(impl<T:AllocMultivector,N> for Multivector);

//
//Sum and Product
//

impl_fold!(impl<T:AllocBlade,U:AllocBlade,N,G> Sum<Blade<T,N,G>> for Blade<U,N,G>);
impl_fold!(impl<T:AllocEven,U:AllocEven,N> Sum<Even<T,N>> for Even<U,N>);
impl_fold!(impl<T:AllocOdd,U:AllocOdd,N> Sum<Odd<T,N>> for Odd<U,N>);
impl_fold!(impl<T:AllocMultivector,U:AllocMultivector,N> Sum<Multivector<T,N>> for Multivector<U,N>);

impl_fold!(impl<T:AllocEven,U:AllocEven,N> Product<Even<T,N>> for Even<U,N>);
impl_fold!(impl<T:AllocBlade,U:AllocMultivector,N,G> Product<Blade<T,N,G>> for Multivector<U,N>);
impl_fold!(impl<T:AllocMultivector,U:AllocMultivector,N> Product<Multivector<T,N>> for Multivector<U,N>);

//
//Zero
//

//currently, this only works with static allocation, but once we have specialization and
//can implement addition between dynamics with different dimensions, we can change that

impl<T:AllocBlade<N,G>+Zero, N:DimName, G:DimName> Zero for Blade<T,N,G> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
    fn set_zero(&mut self) { self.iter_mut().for_each(|x| x.set_zero()) }
}

impl<T:AllocEven<N>+Zero, N:DimName> Zero for Even<T,N> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
    fn set_zero(&mut self) { self.iter_mut().for_each(|x| x.set_zero()) }
}

impl<T:AllocOdd<N>+Zero, N:DimName> Zero for Odd<T,N> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
    fn set_zero(&mut self) { self.iter_mut().for_each(|x| x.set_zero()) }
}

impl<T:AllocMultivector<N>+Zero, N:DimName> Zero for Multivector<T,N> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
    fn set_zero(&mut self) { self.iter_mut().for_each(|x| x.set_zero()) }
}

//
//Neg
//

//don't really know what unary op we'd do besides neg, but here's a general macro anyway :)
macro_rules! impl_unary_ops {
    (
        impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident
        with $Op2:ident.$op2:ident();
        $($a:lifetime)?
    ) => {

        impl<$($a,)? T, U, $($N:Dim),*> $Op for $(&$a)? $Ty<T,$($N),*>
        where
            T: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            T: $Op2<$($a, )? Output=U>
        {

            type Output = $Ty<U,$($N),*>;

            fn $op(self) -> $Ty<U,$($N),*> {
                let mut dest = uninit!(self, Self::Output);
                for (t, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t.$op2());
                }

                $Ty { data: unsafe { dest.assume_init() } }
            }

        }

    };

    //do for value and reference
    (impl<T:$Alloc:ident,$($N:ident),*> $Op:ident.$op:ident() for $Ty:ident with $Ref:ident.$ref:ident()) => {
        impl_unary_ops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Op.$op()  ;   );
        impl_unary_ops!(impl<T:$Alloc,$($N),*> $Op.$op() for $Ty with $Ref.$ref(); 'a);
    };
}

impl_unary_ops!(impl<T:AllocBlade,N,G> Neg.neg() for Blade with RefNeg.ref_neg());
impl_unary_ops!(impl<T:AllocEven,N> Neg.neg() for Even with RefNeg.ref_neg());
impl_unary_ops!(impl<T:AllocOdd,N> Neg.neg() for Odd with RefNeg.ref_neg());
impl_unary_ops!(impl<T:AllocMultivector,N> Neg.neg() for Multivector with RefNeg.ref_neg());

//
//Scalar Multiplication and Division
//

macro_rules! impl_scalar_ops {

    (
        impl<T:$Alloc:ident, $($N:ident),*>
            $Op:ident.$op:ident(), $Scale:ident.$scale:ident(), $Op2:ident.$op2:ident()
        for $Ty:ident; $($a:lifetime)?
    ) => {

        impl<$($a,)? T1,T2,U,$($N:Dim),*> $Scale<T2> for $(&$a)? $Ty<T1,$($N),*>
        where
            T1: $Alloc<$($N),*>,
            T2: Clone,
            U: $Alloc<$($N),*>,
            T1: $Op2<$($a, )? T2, Output=U>,
        {

            type Output = $Ty<U,$($N),*>;

            fn $scale(self, t2: T2) -> $Ty<U,$($N),*> {
                let mut dest = uninit!(self, Self::Output);
                for (t1, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op2(t2.clone()));
                }

                $Ty { data: unsafe { dest.assume_init() } }
            }

        }

        impl<$($a,)? T,U,$($N:Dim),*> $Op<T> for $(&$a)? $Ty<T,$($N),*>
        where
            T: $Alloc<$($N),*>+Clone,
            U: $Alloc<$($N),*>,
            T: $Op2<$($a, )? T, Output=U>
        {
            type Output = $Ty<U,$($N),*>;
            fn $op(self, t2: T) -> $Ty<U,$($N),*> { self.$scale(t2) }
        }

        impl<$($a,)? 'b, T,U,$($N:Dim),*> $Op<&'b T> for $(&$a)? $Ty<T,$($N),*>
        where
            T: $Alloc<$($N),*>,
            U: $Alloc<$($N),*>,
            T: $Op2<$($a, )? &'b T, Output=U>
        {
            type Output = $Ty<U,$($N),*>;
            fn $op(self, t2: &'b T) -> $Ty<U,$($N),*> { self.$scale(t2) }
        }

    };

    //do every combination of reference and value
    (
        impl<T:$Alloc:ident, $($N:ident),*>
            $Op:ident.$op:ident(), $Scale:ident.$scale:ident(), $Ref:ident.$ref:ident()
            for $Ty:ident
    ) => {
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op(), $Scale.$scale(), $Op.$op() for $Ty;);
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> $Op.$op(), $Scale.$scale(), $Ref.$ref() for $Ty; 'a);
    };

    (impl<T:$Alloc:ident, $($N:ident),*> for $Ty:ident) => {
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> Mul.mul(), Scale.scale(), RefMul.ref_mul() for $Ty);
        impl_scalar_ops!(impl<T:$Alloc, $($N),*> Div.div(), InvScale.inv_scale(), RefDiv.ref_div() for $Ty);
    };

}

impl_scalar_ops!(impl<T:AllocBlade,N,G> for Blade);
impl_scalar_ops!(impl<T:AllocEven,N> for Even);
impl_scalar_ops!(impl<T:AllocOdd,N> for Odd);
impl_scalar_ops!(impl<T:AllocMultivector,N> for Multivector);

macro_rules! impl_scalar_assign_binops {
    (impl<T:$Alloc:ident, $($N:ident),*> $Op:ident.$op:ident() for $Ty:ident) => {

        impl<T:$Alloc<$($N),*>+$Op<T>+Clone, $($N:Dim),*> $Op<T> for $Ty<T, $($N),*> {
            fn $op(&mut self, rhs: T) {
                //simple enough...
                for t1 in self {
                    t1.$op(rhs.clone());
                }
            }
        }

        impl<'a, T:$Alloc<$($N),*>+$Op<&'a T>, $($N:Dim),*> $Op<&'a T> for $Ty<T, $($N),*> {
            fn $op(&mut self, rhs: &'a T) {
                //simple enough...
                for t1 in self {
                    t1.$op(rhs);
                }
            }
        }

    }
}

impl_scalar_assign_binops!(impl<T:AllocBlade,N,G> MulAssign.mul_assign() for Blade);
impl_scalar_assign_binops!(impl<T:AllocBlade,N,G> DivAssign.div_assign() for Blade);
impl_scalar_assign_binops!(impl<T:AllocEven,N> MulAssign.mul_assign() for Even);
impl_scalar_assign_binops!(impl<T:AllocEven,N> DivAssign.div_assign() for Even);
impl_scalar_assign_binops!(impl<T:AllocOdd,N> MulAssign.mul_assign() for Odd);
impl_scalar_assign_binops!(impl<T:AllocOdd,N> DivAssign.div_assign() for Odd);
impl_scalar_assign_binops!(impl<T:AllocMultivector,N> MulAssign.mul_assign() for Multivector);
impl_scalar_assign_binops!(impl<T:AllocMultivector,N> DivAssign.div_assign() for Multivector);

impl_forward_scalar_binops!(impl<T:AllocBlade,N,G> Mul.mul() for Blade);
// impl_forward_scalar_binops!(impl<T:AllocBlade,N,G> Div.div() for Blade);
impl_forward_scalar_binops!(impl<T:AllocEven,N> Mul.mul() for Even);
// impl_forward_scalar_binops!(impl<T:AllocEven,N> Div.div() for Even);
impl_forward_scalar_binops!(impl<T:AllocOdd,N> Mul.mul() for Odd);
// impl_forward_scalar_binops!(impl<T:AllocOdd,N> Div.div() for Odd);
impl_forward_scalar_binops!(impl<T:AllocMultivector,N> Mul.mul() for Multivector);
// impl_forward_scalar_binops!(impl<T:AllocMultivector,N> Div.div() for Multivector);

//
//MulAssign and DivAssign
//

macro_rules! impl_mul_assign {
    (
        $Ty1:ident<T:$Alloc1:ident $(,$N1:ident)*> *=
        $(&$a:lifetime)? $Ty2:ident<T:$Alloc2:ident $(,$N2:ident)*>; $($N:ident)*
    ) => {

        impl<$($a,)? T $(,$N:Dim)*> MulAssign<$(&$a)? $Ty2<T$(,$N2)*>> for $Ty1<T $(,$N1)*> where
            T: $Alloc1<$($N1),*> + $Alloc2<$($N2),*> + AddGroup + AllRefMul<T,AllOutput=T>
        {
            fn mul_assign(&mut self, rhs: $(&$a)? $Ty2<T$(,$N2)*>) {
                *self = &*self * rhs
            }
        }

    }
}


impl_mul_assign!( Multivector<T:AllocMultivector,N> *= Blade<T:AllocBlade,N,G>; N G);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= &'a Blade<T:AllocBlade,N,G>; N G);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= Even<T:AllocEven,N>; N);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= &'a Even<T:AllocEven,N>; N);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= Odd<T:AllocOdd,N>; N);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= &'a Odd<T:AllocOdd,N>; N);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= Multivector<T:AllocMultivector,N>; N);
impl_mul_assign!( Multivector<T:AllocMultivector,N> *= &'a Multivector<T:AllocMultivector,N>; N);


impl_mul_assign!( Even<T:AllocEven,N> *= Even<T:AllocEven,N>; N);
impl_mul_assign!( Even<T:AllocEven,N> *= &'a Even<T:AllocEven,N>; N);


macro_rules! impl_pow {
    ($Ty:ident<T:$Alloc:ident $(,$N:ident)*>) => {
        impl<T:$Alloc<$($N),*>+RefUnitRing $(, $N:Dim)*> $Ty<T $(,$N)*> {

            pub fn powu(self, p:u32) -> Self {
                let n = self.dim_generic();
                repeated_doubling(self, Self::one_generic(n), p)
            }

            pub fn powi(self, p:i32) -> Self where Self:ClosedInv {
                let n = self.dim_generic();
                repeated_doubling_inv(self, Self::one_generic(n), p)
            }

        }
    };
}

impl_pow!(Even<T:AllocEven,N>);
impl_pow!(Multivector<T:AllocMultivector,N>);
