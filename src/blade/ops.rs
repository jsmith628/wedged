
use super::*;

//
//Index Ops
//

//Currently, we just to indexing wrt `usize`. There may be additions in the future, but
//unlike with Matrices or slices, ranges don't really make much sense, and while indexing wrt
//basis blades _may_ make sense, it's slow *and* we have to deal with a potential minus sign.

impl<T:Alloc<N,G>, N:Dim, G:Dim> Index<usize> for Blade<T,N,G> {
    type Output = T;
    fn index(&self, i: usize) -> &T { &self.data[i] }
}

impl<T:Alloc<N,G>, N:Dim, G:Dim> IndexMut<usize> for Blade<T,N,G> {
    fn index_mut(&mut self, i: usize) -> &mut T { &mut self.data[i] }
}

//
//Addition and Subtraction
//

//we do this as a macro to make it easier to do with self and rhs being both references and
//values in the macro calls
macro_rules! check_add_dim_grade {
    ($self:ident, $rhs:ident) => {

        //for ease of use
        let (d1, d2) = ($self.dim_generic(), $rhs.dim_generic());
        let (g1, g2) = ($self.grade_generic(), $rhs.grade_generic());

        //if the dims or grades don't match, panic
        //this check should optimize away for statically allocated blades
        //TODO: maybe have blades with same grade but different dim add together once we
        //have specialization and can use `Zero` conditionally
        if d1!=d2 { panic!("Cannot add blades of different dimension: {}!={}", d1.value(), d2.value()); }
        if g1!=g2 { panic!("Cannot add blades of different grade: {}!={}", g1.value(), g2.value()); }

    }
}

macro_rules! impl_binops {

    //implements operation with optional references
    ($Op:ident.$op:ident(); $($a:lifetime)?; $($b:lifetime)?) => {

        impl<$($a,)? $($b,)? T1,T2,U,N:Dim,G:Dim> $Op<$(&$b)? Blade<T2,N,G>> for $(&$a)? Blade<T1,N,G>
        where
            T1: Alloc<N,G>,
            T2: Alloc<N,G>,
            U: Alloc<N,G>,
            $(&$a)? T1: $Op<$(&$b)? T2, Output=U>
        {

            type Output = Blade<U,N,G>;

            fn $op(self, rhs: $(&$b)? Blade<T2,N,G>) -> Blade<U,N,G> {

                check_add_dim_grade!(self, rhs);

                //TODO: if either T1 or T2 has the same size as U, reuse the storage
                //Theoretically, the compiler _should_ optimize this allocation away if it is
                //unnecessary, but we won't know until some benchmarking
                let mut dest = Allocate::<U,N,G>::uninit(self.dim_generic(), self.grade_generic());
                for ((t1, t2), u) in self.into_iter().zip(rhs).zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op(t2));
                }

                Blade { data: unsafe { dest.assume_init() } }

            }

        }

    };

    //do every combination of reference and value
    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_binops!($Op.$op();   ;   );
            impl_binops!($Op.$op(); 'a;   );
            impl_binops!($Op.$op();   ; 'b);
            impl_binops!($Op.$op(); 'a; 'b);
        )*
    };

}

macro_rules! impl_assign_binops {

    //implements operation with an optional reference
    ($Op:ident.$op:ident(); $($a:lifetime)?) => {

        impl<$($a,)? T1,T2,N:Dim,G:Dim> $Op<$(&$a)? Blade<T2,N,G>> for Blade<T1,N,G>
        where
            T1: Alloc<N,G> + $Op<$(&$a)? T2>,
            T2: Alloc<N,G>
        {

            fn $op(&mut self, rhs: $(&$a)? Blade<T2,N,G>) {

                check_add_dim_grade!(self, rhs);

                //simple enough...
                for (t1, t2) in self.iter_mut().zip(rhs) {
                    t1.$op(t2);
                }

            }

        }

    };

    //do for value and reference
    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_assign_binops!($Op.$op();   );
            impl_assign_binops!($Op.$op(); 'a);
        )*
    };

}

impl_binops!(Add.add(), Sub.sub());
impl_assign_binops!(AddAssign.add_assign(), SubAssign.sub_assign());

//
//Zero
//

//currently, this only works with static allocation, but once we have specialization and
//can implement addition between dynamics with different dimensions, we can change that
impl<T:Alloc<N,G>+Zero, N:DimName, G:DimName> Zero for Blade<T,N,G> {
    fn zero() -> Self { Self::zeroed() }
    fn is_zero(&self) -> bool { self.iter().all(|e| e.is_zero()) }
}

//
//Neg
//

macro_rules! impl_unary_ops {
    ($Op:ident.$op:ident(); $($a:lifetime)?) => {
        impl<$($a,)? T,U,N:Dim,G:Dim> $Op for $(&$a)? Blade<T,N,G>
        where
            T: Alloc<N,G>,
            U: Alloc<N,G>,
            $(& $a)? T: $Op<Output=U>
        {

            type Output = Blade<U,N,G>;

            fn $op(self) -> Blade<U,N,G> {
                let mut dest = Allocate::<U,N,G>::uninit(self.dim_generic(), self.grade_generic());
                for (t, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t.$op());
                }

                Blade { data: unsafe { dest.assume_init() } }
            }

        }

    };

    //do for value and reference
    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_unary_ops!($Op.$op();   );
            impl_unary_ops!($Op.$op(); 'a);
        )*
    };
}

impl_unary_ops!(Neg.neg());

//
//Scalar Multiplication and Division
//

macro_rules! impl_scalar_ops {

    ($Op:ident.$op:ident(); $($a:lifetime)?; $($b:lifetime)?) => {

        impl<$($a,)? $($b,)? T,U,N:Dim,G:Dim> $Op<$(&$b)? T> for $(&$a)? Blade<T,N,G>
        where
            T: Alloc<N,G>,
            U: Alloc<N,G>,
            $(&$a)? T: $Op<$(&$b)? T, Output=U>,
            $(&$b)? T: Clone
        {

            type Output = Blade<U,N,G>;

            fn $op(self, t2: $(&$b)? T) -> Blade<U,N,G> {

                let mut dest = Allocate::<U,N,G>::uninit(self.dim_generic(), self.grade_generic());
                for (t1, u) in self.into_iter().zip(dest.borrow_mut()) {
                    *u = MaybeUninit::new(t1.$op(<$(&$b)? T as Clone>::clone(&t2)));
                }

                Blade { data: unsafe { dest.assume_init() } }

            }

        }

    };

    //do every combination of reference and value
    ($($Op:ident.$op:ident()),*) => {
        $(
            impl_scalar_ops!($Op.$op();   ;   );
            impl_scalar_ops!($Op.$op(); 'a;   );
            impl_scalar_ops!($Op.$op();   ; 'b);
            impl_scalar_ops!($Op.$op(); 'a; 'b);
        )*
    };

}

impl_scalar_ops!(Mul.mul(), Div.div());
