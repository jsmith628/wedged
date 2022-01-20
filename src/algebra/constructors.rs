
use super::*;
use crate::subspace::*;

macro_rules! impl_generic_constructors {

    (pub fn new($($n:ident:$N:ident),*) -> Self {  }) => {
        impl_generic_constructors!(
            pub fn new($($n:$N),*) -> Self {
                |iter| Self { data: Allocate::<Self>::from_iterator($($n, )* iter) }
            }
        );
    };

    (pub fn new($($n:ident:$N:ident),*) -> Self { |$iter:ident| $from_iter:expr }) => {
        /// Constructs a value with elements from an iterator using a generic shape
        pub fn from_iter_generic<I:IntoIterator<Item=T>>($($n: $N, )* $iter: I) -> Self {
            $from_iter
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

    }
}

macro_rules! impl_zero_basis_constructors {

    (pub fn new($($n:ident:$N:ident),*) -> Self {}) => {
        impl_zero_basis_constructors!(
            pub fn new($($n:$N),*) -> Self {
                Self::from_iter_generic($($n, )* repeat_with(|| T::zero()))
            }
        );
    };

    (pub fn new($($n:ident:$N:ident),*) -> Self { $expr:expr }) => {
        /// Constructs a blade with all components set to [zero](Zero::zero) using a generic shape
        pub fn zeroed_generic($($n: $N),*) -> Self where T:Zero {
            $expr
        }

        /// Uses a generic shape to returns an element where the `i`th value is one and the rest are zeroes
        ///
        /// Panics if `i` is out of range
        pub fn basis_generic($($n: $N, )* i: usize) -> Self where T:Zero+One {
            let mut basis = Self::zeroed_generic($($n),*);
            basis.data[i] = T::one();
            basis
        }
    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {
    impl_generic_constructors!( pub fn new(n:N, g:G) -> Self { } );
    impl_zero_basis_constructors!( pub fn new(n:N, g:G) -> Self { } );
}

impl<T:AllocSimpleBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {
    impl_generic_constructors!(
        pub fn new(n:N, g:G) -> Self {
            |iter| Self::from_inner_unchecked(Blade::from_iter_generic(n, g, iter))
        }
    );
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {
    /// Constructs a blade with all components set to [zero](Zero::zero) using a generic shape
    pub fn zeroed_generic(n:N, g:G) -> Self where T:Zero {
        Self::from_inner_unchecked(Blade::zeroed_generic(n, g))
    }

    /// Returns the `i`th basis element or panics if `i` is out of range
    pub fn basis_generic(n:N, g:G, i: usize) -> Self where T:Zero+One {
        Self::from_inner_unchecked(Blade::basis_generic(n, g, i))
    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {
    /// Returns the `i`th basis element or panics if `i` is out of range
    pub fn basis_generic(n:N, g:G, i: usize) -> Self where T:Zero+One {
        Self::from_inner_unchecked(Blade::basis_generic(n, g, i))
    }
}

impl<T:AllocEven<N>, N:Dim> Even<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );
    impl_zero_basis_constructors!( pub fn new(n:N) -> Self { } );

    /// Uses a generic shape to construct the multiplicative identity
    pub fn one_generic(n: N) -> Self where T:One+Zero {
        Self::from_iter_generic(n, once_with(T::one).chain(repeat_with(T::zero)))
    }

}

impl<T:AllocOdd<N>, N:Dim> Odd<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );
    impl_zero_basis_constructors!( pub fn new(n:N) -> Self { } );
}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {
    impl_generic_constructors!( pub fn new(n:N) -> Self { } );
    impl_zero_basis_constructors!( pub fn new(n:N) -> Self { } );

    /// Uses a generic shape to construct the multiplicative identity
    pub fn one_generic(n: N) -> Self where T:One+Zero {
        Self::from_iter_generic(n, once_with(T::one).chain(repeat_with(T::zero)))
    }
}

//TODO: fix the documentation

macro_rules! impl_general_constructors {
    ($($args:ident),*; $($call:tt)*) => {

        ///
        /// Constructs a value using elements from an iterator
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
        pub fn from_iterator<I:IntoIterator<Item=T>>($($args: usize,)* iter: I) -> Self {
            Self::from_iter_generic($($call)*, iter)
        }

        ///
        /// Constructs a value using a function mapping an index to an element
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
        pub fn from_index_fn<F: FnMut(usize)->T>($($args: usize,)* f: F) -> Self {
            Self::from_index_fn_generic($($call)*, f)
        }

        ///
        /// Constructs a value where every component is the given element
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
        pub fn from_element($($args: usize,)* x:T) -> Self where T:Clone {
            Self::from_element_generic($($call)*, x)
        }

        ///
        /// Constructs an elements by cloning values from a slice
        ///
        /// Panics if not enough values are provided
        ///
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// let values = [6, 2, 8, 3];
        ///
        /// let v1 = Vec4::from_slice(&values);
        /// let v2 = VecD::from_slice(4, &values);
        /// let q = Even3::from_slice(&values);
        ///
        /// assert_eq!(v1.as_slice(), &values);
        /// assert_eq!(v2.as_slice(), &values);
        /// assert_eq!(q.as_slice(), &values);
        ///
        /// ```
        ///
        pub fn from_slice($($args: usize,)* data: &[T]) -> Self where T:Clone {
            Self::from_slice_generic($($call)*, data)
        }

        ///
        /// Constructs an elements by moving values from a `Vec`
        ///
        /// Panics if not enough values are provided
        ///
        /// ```
        /// # use galgebra::algebra::*;
        ///
        /// let values = vec![6, 2, 8, 3];
        ///
        /// let v1 = Vec4::from_vec(values.clone());
        /// let v2 = VecD::from_vec(4, values.clone());
        /// let q = Even3::from_vec(values.clone());
        ///
        /// assert_eq!(v1.as_slice(), &*values);
        /// assert_eq!(v2.as_slice(), &*values);
        /// assert_eq!(q.as_slice(), &*values);
        ///
        /// ```
        ///
        pub fn from_vec($($args: usize,)* data: Vec<T>) -> Self where T:Clone {
            Self::from_vec_generic($($call)*, data)
        }
    };
}

macro_rules! impl_general_zero_basis_constructors {
    ($($args:ident),*; $($call:tt)*) => {

        ///
        ///Constructs a value with all components set to [zero](Zero::zero)
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
        pub fn zeroed($($args: usize),*) -> Self where T:Zero {
            Self::zeroed_generic($($call)*)
        }

        /// Returns an element where the `i`th value is one and the rest are zeroes
        ///
        /// Panics if `i` is out of range
        pub fn basis($($args: usize,)* i:usize) -> Self where T:Zero+One {
            Self::basis_generic($($call)*, i)
        }

    };
}

///Constructors for statically sized blades
impl<T:AllocBlade<N,G>, N:DimName, G:DimName> Blade<T,N,G> {
    impl_general_constructors!(; N::name(), G::name());
    impl_general_zero_basis_constructors!(; N::name(), G::name());
}
impl<T:AllocSimpleBlade<N,G>, N:DimName, G:DimName> SimpleBlade<T,N,G> {
    impl_general_constructors!(; N::name(), G::name());
}
impl<T:AllocBlade<N,G>, N:DimName, G:DimName> SimpleBlade<T,N,G> {
    impl_general_zero_basis_constructors!(; N::name(), G::name());
}

///Constructors for blades with dynamic dimension
impl<T:AllocBlade<Dynamic,G>, G:DimName> Blade<T,Dynamic,G> {
    impl_general_constructors!(n; Dynamic::new(n), G::name());
    impl_general_zero_basis_constructors!(n; Dynamic::new(n), G::name());
}
impl<T:AllocSimpleBlade<Dynamic,G>, G:DimName> SimpleBlade<T,Dynamic,G> {
    impl_general_constructors!(n; Dynamic::new(n), G::name());
}
impl<T:AllocBlade<Dynamic,G>, G:DimName> SimpleBlade<T,Dynamic,G> {
    impl_general_zero_basis_constructors!(n; Dynamic::new(n), G::name());
}

///Constructors for blades with dynamic grade
impl<T:AllocBlade<N,Dynamic>, N:DimName> BladeN<T,N> {
    impl_general_constructors!(g; N::name(), Dynamic::new(g));
    impl_general_zero_basis_constructors!(g; N::name(), Dynamic::new(g));
}

///Constructors for blades with dynamic dimension and grade
impl<T:AllocBlade<Dynamic,Dynamic>> BladeD<T> {
    impl_general_constructors!(n,g; Dynamic::new(n), Dynamic::new(g));
    impl_general_zero_basis_constructors!(n,g; Dynamic::new(n), Dynamic::new(g));
}

///Constructors for statically sized rotors
impl<T:AllocEven<N>, N:DimName> Even<T, N> {
    impl_general_constructors!(; N::name());
    impl_general_zero_basis_constructors!(; N::name());
}

///Constructors for rotors with dynamic dimension
impl<T:AllocEven<Dynamic>> EvenD<T> {
    impl_general_constructors!(n; Dynamic::new(n));
    impl_general_zero_basis_constructors!(n; Dynamic::new(n));

    //Constructs the multiplicative identity element using a dynamic dimension
    pub fn one_dyn(n: usize) -> Self where T:One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

//Constructors for statically sized odd-values
impl<T:AllocOdd<N>, N:DimName> Odd<T, N> {
    impl_general_constructors!(; N::name());
    impl_general_zero_basis_constructors!(; N::name());
}

//Constructors for odd values with dynamic dimension
impl<T:AllocOdd<Dynamic>> OddD<T> {
    impl_general_constructors!(n; Dynamic::new(n));
    impl_general_zero_basis_constructors!(n; Dynamic::new(n));
}

///Constructors for statically sized rotors
impl<T:AllocMultivector<N>, N:DimName> Multivector<T, N> {
    impl_general_constructors!(; N::name());
    impl_general_zero_basis_constructors!(; N::name());
}

///Constructors for rotors with dynamic dimension
impl<T:AllocMultivector<Dynamic>> MultivectorD<T> {
    impl_general_constructors!(n; Dynamic::new(n));
    impl_general_zero_basis_constructors!(n; Dynamic::new(n));

    //Constructs the multiplicative identity element using a dynamic dimension
    pub fn one_dyn(n: usize) -> Self where T:One+Zero {
        Self::one_generic(Dynamic::new(n))
    }
}

macro_rules! impl_new {

    //starts the loop
    ($($ty:ident::new($($arg:ident),*);)*) => {
        $(
            impl<T> $ty<T> {
                #[doc = new_docs!($ty::new($($arg),*);)]
                pub const fn new($($arg: T),*) -> $ty<T> {
                    $ty { data: [ $($arg),* ] }
                }
            }
        )*
    };
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

    pub fn new(x:T) -> Self {
        Self::from_iterator(std::iter::once(x))
    }

}

impl<T:AllocBlade<N,N>, N:DimName> PsuedoScalar<T,N> {

    pub fn new_psuedoscalar(x:T) -> Self {
        Self::from_iterator(std::iter::once(x))
    }

    pub fn unit_psuedoscalar() -> Self where T:One {
        Self::from_iterator(repeat_with(|| T::one()))
    }

}
