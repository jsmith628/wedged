
use super::*;

macro_rules! impl_generic_constructors {
    (pub fn new($($n:ident:$N:ident),*) -> Self { }) => {
        /// Constructs a value with elements from an iterator using a generic shape
        pub fn from_iter_generic<I:IntoIterator<Item=T>>($($n: $N, )* iter: I) -> Self {
            Self { data: Allocate::<Self>::from_iterator($($n, )* iter) }
        }

        /// Constructs a value from an index function using a generic shape
        pub fn from_index_fn_generic<F: FnMut(usize)->T>($($n: $N, )* f: F) -> Self {
            Self::from_iter_generic($($n, )* (0..).map(f))
        }

        /// Constructs a value filled with given element using a generic shape
        pub fn from_element_generic($($n: $N, )* x:T) -> Self where T:Clone {
            Self::from_iter_generic($($n, )* repeat(x))
        }

        /// Constructs a value cloned from a slice
        pub fn from_slice_generic($($n: $N, )* data: &[T]) -> Self where T:Clone {
            Self::from_iter_generic($($n, )* data.iter().cloned())
        }

        /// Constructs a value from a [`Vec`]
        pub fn from_vec_generic($($n: $N, )* data: Vec<T>) -> Self where T:Clone {
            Self::from_iter_generic($($n, )* data)
        }

        /// Constructs a blade with all components set to [zero](Zero::zero) using a generic shape
        pub fn zeroed_generic($($n: $N),*) -> Self where T:Zero {
            Self::from_iter_generic($($n, )* repeat_with(|| T::zero()))
        }

        /// Returns the `i`th basis element or panics if `i` is out of range
        pub fn basis_generic($($n: $N, )* i: usize) -> Self where T:Zero+One {
            let mut basis = Self::zeroed_generic($($n),*);
            basis[i] = T::one();
            basis
        }

    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {
    impl_generic_constructors!( pub fn new(n:N, g:G) -> Self { } );
}

impl<T:AllocEven<N>, N:Dim> Even<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );

    pub fn one_generic(n: N) -> Self where T:One+Zero {
        Self::from_iter_generic(n, once_with(T::one).chain(repeat_with(T::zero)))
    }

}

impl<T:AllocOdd<N>, N:Dim> Odd<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );
}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );

    pub fn one_generic(n: N) -> Self where T:One+Zero {
        Self::from_iter_generic(n, once_with(T::one).chain(repeat_with(T::zero)))
    }
}

//TODO: fix the documentation

macro_rules! impl_general_constructors {
    (pub fn new($($args:tt)*) -> Self { Self::new_generic($($call:tt)*) }) => {

        ///
        /// Constructs a blade with elements from an iterator
        ///
        /// Panics if the iterator has too few elements to fill in the blade
        ///
        /// # Examples
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// let array = [0, 1, 2, 3, 4, 5];
        ///
        /// let v1 = Vec6::from_iterator(0..); //static dim, static grade
        /// let v2 = VecD::from_iterator(6, 0..); //dynamic dim, static grade
        /// let v3 = Blade6::from_iterator(1, 0..); //static dim, dynamic grade
        /// let v4 = BladeD::from_iterator(6, 1, 0..); //dynamic dim, dynamic grade
        ///
        /// assert_eq!(v1.as_slice(), &array);
        /// assert_eq!(v2.as_slice(), &array);
        /// assert_eq!(v3.as_slice(), &array);
        /// assert_eq!(v4.as_slice(), &array);
        ///
        /// ```
        ///
        pub fn from_iterator<I:IntoIterator<Item=T>>($($args)* iter: I) -> Self {
            Self::from_iter_generic($($call)*, iter)
        }

        ///
        /// Constructs a blade from a function mapping an index to an element
        ///
        /// # Examples
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// //computes the nth fibonnacci number
        /// fn fib(n: usize) -> usize {
        ///     if n <= 1 {
        ///         1
        ///     } else {
        ///         fib(n-1) + fib(n-2)
        ///     }
        /// }
        ///
        /// //5D bivector, so 10 elements
        /// let array = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
        ///
        /// let b1 = BiVec5::from_index_fn(fib); //static dim, static grade
        /// let b2 = BiVecD::from_index_fn(5, fib); //dynamic dim, static grade
        /// let b3 = Blade5::from_index_fn(2, fib); //static dim, dynamic grade
        /// let b4 = BladeD::from_index_fn(5, 2, fib); //dynamic dim, dynamic grade
        ///
        /// assert_eq!(b1.as_slice(), &array);
        /// assert_eq!(b2.as_slice(), &array);
        /// assert_eq!(b3.as_slice(), &array);
        /// assert_eq!(b4.as_slice(), &array);
        ///
        ///```
        ///
        pub fn from_index_fn<F: FnMut(usize)->T>($($args)* f: F) -> Self {
            Self::from_index_fn_generic($($call)*, f)
        }

        ///
        /// Constructs a blade where every component is the given element
        ///
        /// # Examples
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// //4D Trivector, so 4 elements
        /// let array = [6.28; 4];
        ///
        /// let t1 = TriVec4::from_element(6.28); //static dim, static grade
        /// let t2 = TriVecD::from_element(4, 6.28); //dynamic dim, static grade
        /// let t3 = Blade4::from_element(3, 6.28); //static dim, dynamic grade
        /// let t4 = BladeD::from_element(4, 3, 6.28); //dynamic dim, dynamic grade
        ///
        /// assert_eq!(t1.as_slice(), &array);
        /// assert_eq!(t2.as_slice(), &array);
        /// assert_eq!(t3.as_slice(), &array);
        /// assert_eq!(t4.as_slice(), &array);
        ///
        ///```
        ///
        pub fn from_element($($args)* x:T) -> Self where T:Clone {
            Self::from_element_generic($($call)*, x)
        }

        pub fn from_slice($($args)* data: &[T]) -> Self where T:Clone {
            Self::from_slice_generic($($call)*, data)
        }

        pub fn from_vec($($args)* data: Vec<T>) -> Self where T:Clone {
            Self::from_vec_generic($($call)*, data)
        }

        ///
        ///Constructs a blade with all components set to [zero](Zero::zero)
        ///
        /// # Examples
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// let array = [0.0; 4];
        ///
        /// let v1 = Vec4::<f64>::zeroed(); //static dim, static grade
        /// let v2 = VecD::<f64>::zeroed(4); //dynamic dim, static grade
        /// let v3 = Blade4::<f64>::zeroed(1); //static dim, dynamic grade
        /// let v4 = BladeD::<f64>::zeroed(4, 1); //dynamic dim, dynamic grade
        ///
        /// assert_eq!(v1.as_slice(), &array);
        /// assert_eq!(v2.as_slice(), &array);
        /// assert_eq!(v3.as_slice(), &array);
        /// assert_eq!(v4.as_slice(), &array);
        ///
        ///```
        ///
        pub fn zeroed($($args)*) -> Self where T:Zero {
            Self::zeroed_generic($($call)*)
        }

        pub fn basis($($args)* i:usize) -> Self where T:Zero+One {
            Self::basis_generic($($call)*, i)
        }

    };
}

///Constructors for statically sized blades
impl<T:AllocBlade<N,G>, N:DimName, G:DimName> Blade<T,N,G> {

    impl_general_constructors!(
        pub fn new() -> Self {
            Self::new_generic(N::name(), G::name())
        }
    );

}

///Constructors for blades with dynamic dimension
impl<T:AllocBlade<Dynamic,G>, G:DimName> Blade<T,Dynamic,G> {

    impl_general_constructors!(
        pub fn new(n:usize,) -> Self {
            Self::new_generic(Dynamic::new(n), G::name())
        }
    );

}

///Constructors for blades with dynamic grade
impl<T:AllocBlade<N,Dynamic>, N:DimName> BladeN<T,N> {

    impl_general_constructors!(
        pub fn new(g:usize,) -> Self {
            Self::new_generic(N::name(), Dynamic::new(g))
        }
    );

}

///Constructors for blades with dynamic dimension and grade
impl<T:AllocBlade<Dynamic,Dynamic>> BladeD<T> {

    impl_general_constructors!(
        pub fn new(n:usize,g:usize,) -> Self {
            Self::new_generic(Dynamic::new(n), Dynamic::new(g))
        }
    );

}

///Constructors for statically sized rotors
impl<T:AllocEven<N>, N:DimName> Even<T, N> {
    impl_general_constructors!(
        pub fn new() -> Self {
            Self::new_generic(N::name())
        }
    );
}

///Constructors for rotors with dynamic dimension
impl<T:AllocEven<Dynamic>> EvenD<T> {
    impl_general_constructors!(
        pub fn new(n:usize,) -> Self {
            Self::new_generic(Dynamic::new(n))
        }
    );

    pub fn one_dyn(n: usize) -> Self where T:One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

//Constructors for statically sized odd-values
impl<T:AllocOdd<N>, N:DimName> Odd<T, N> {
    impl_general_constructors!(
        pub fn new() -> Self {
            Self::new_generic(N::name())
        }
    );
}

//Constructors for odd values with dynamic dimension
impl<T:AllocOdd<Dynamic>> OddD<T> {
    impl_general_constructors!(
        pub fn new(n:usize,) -> Self {
            Self::new_generic(Dynamic::new(n))
        }
    );
}

///Constructors for statically sized rotors
impl<T:AllocMultivector<N>, N:DimName> Multivector<T, N> {
    impl_general_constructors!(
        pub fn new() -> Self {
            Self::new_generic(N::name())
        }
    );
}

///Constructors for rotors with dynamic dimension
impl<T:AllocMultivector<Dynamic>> MultivectorD<T> {
    impl_general_constructors!(
        pub fn new(n:usize,) -> Self {
            Self::new_generic(Dynamic::new(n))
        }
    );

    pub fn one_dyn(n: usize) -> Self where T:One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

macro_rules! impl_new {

    //starts the loop
    ($($ty:ident::new($($arg:ident),*);)*) => { $(impl_new!(@vals 0 $($arg)*; $ty);)* };

    //picks out the numbers that will be used in the doc test
    (@vals 0  $arg:ident $($tt:tt)*) => { impl_new!(@vals 1  $($tt)* $arg 6); };
    (@vals 1  $arg:ident $($tt:tt)*) => { impl_new!(@vals 2  $($tt)* $arg 2); };
    (@vals 2  $arg:ident $($tt:tt)*) => { impl_new!(@vals 3  $($tt)* $arg 8); };
    (@vals 3  $arg:ident $($tt:tt)*) => { impl_new!(@vals 4  $($tt)* $arg 3); };
    (@vals 4  $arg:ident $($tt:tt)*) => { impl_new!(@vals 5  $($tt)* $arg 1); };
    (@vals 5  $arg:ident $($tt:tt)*) => { impl_new!(@vals 6  $($tt)* $arg 8); };
    (@vals 6  $arg:ident $($tt:tt)*) => { impl_new!(@vals 7  $($tt)* $arg 5); };
    (@vals 7  $arg:ident $($tt:tt)*) => { impl_new!(@vals 8  $($tt)* $arg 3); };
    (@vals 8  $arg:ident $($tt:tt)*) => { impl_new!(@vals 9  $($tt)* $arg 0); };
    (@vals 9  $arg:ident $($tt:tt)*) => { impl_new!(@vals 10 $($tt)* $arg 7); };
    (@vals 10 $arg:ident $($tt:tt)*) => { impl_new!(@vals 11 $($tt)* $arg 1); };
    (@vals 11 $arg:ident $($tt:tt)*) => { impl_new!(@vals 12 $($tt)* $arg 7); };
    (@vals 12 $arg:ident $($tt:tt)*) => { impl_new!(@vals 13 $($tt)* $arg 9); };
    (@vals 13 $arg:ident $($tt:tt)*) => { impl_new!(@vals 14 $($tt)* $arg 5); };
    (@vals 14 $arg:ident $($tt:tt)*) => { impl_new!(@vals 15 $($tt)* $arg 8); };
    (@vals 15 $arg:ident $($tt:tt)*) => { impl_new!(@vals 16 $($tt)* $arg 6); };
    (@vals 16 $arg:ident $($tt:tt)*) => { impl_new!(@vals 17 $($tt)* $arg 4); };
    (@vals 17 $arg:ident $($tt:tt)*) => { impl_new!(@vals 18 $($tt)* $arg 7); };
    (@vals 18 $arg:ident $($tt:tt)*) => { impl_new!(@vals 19 $($tt)* $arg 6); };
    (@vals 19 $arg:ident $($tt:tt)*) => { impl_new!(@vals 20 $($tt)* $arg 9); };

    //creates the function at the end of the vals loop
    (@vals $n:literal; $ty:ident $($arg:ident $val:literal)*) => {
        impl<T> $ty<T> {
            #[doc = concat!(
                //yes, this is kinda gross, but it *does* work
                "Constructs a [`", stringify!($ty), "`] directly from components\n",
                "\n",
                " # Examples\n",
                "```\n",
                " # use galgebra::algebra::*;",
                "let x = ", stringify!($ty), "::new(", stringify!($($val),*), ");\n",
                "let arr = [", stringify!($($val),*), "];\n",
                "\n",
                "assert_eq!(x.as_slice(), &arr);\n",
                "```"
            )]
            pub const fn new($($arg: T),*) -> $ty<T> {
                $ty { data: [ $($arg),* ] }
            }
        }
    }
}

impl_new!{

    Vec1::new(x);
    Vec2::new(x,y);
    Vec3::new(x,y,z);
    Vec4::new(x,y,z,w);
    Vec5::new(x,y,z,w,a);
    Vec6::new(x,y,z,w,a,b);

    BiVec2::new(x);
    BiVec3::new(x,y,z);
    BiVec4::new(yz,zx,xy,xw,yw,zw);
    BiVec5::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa);
    BiVec6::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa,xb,yb,zb,wb,ab);

    TriVec3::new(x);
    TriVec4::new(x,y,z,w);
    TriVec5::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa);
    TriVec6::new(
        e145, e245, e345, e235, e315, e125, e324, e134, e214, e123,
        e326, e136, e216, e416, e426, e436, e516, e526, e536, e546
    );

    QuadVec4::new(x);
    QuadVec5::new(x,y,z,w,a);
    QuadVec6::new(yz,zx,xy,xw,yw,zw,xa,ya,za,wa,xb,yb,zb,wb,ab);

    PentVec5::new(x);
    PentVec6::new(x,y,z,w,a,b);

    HexVec6::new(x);

    Even0::new(r);
    Even1::new(r);
    Even2::new(r, i);
    Even3::new(w, i,j,k);
    Even4::new(r, yz,zx,xy,xw,yw,zw, i);

    Multivector0::new(r);
    Multivector1::new(r,x);
    Multivector2::new(r, x,y, i);
    Multivector3::new(r, x,y,z, yz,zx,xy, i);

}

impl<T:AllocBlade<N,U0>, N:DimName> Scalar<T,N> {

    pub fn new(x:T) -> Scalar<T,N> {
        Self::from_iterator(std::iter::once(x))
    }

}
