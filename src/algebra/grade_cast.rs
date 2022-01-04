use super::*;

impl<T:AllocBlade<N,G>+Zero, N:Dim, G:Dim> Blade<T,N,G> {

    pub fn into_even(self) -> Even<T, N> where T:AllocEven<N> {
        Even::from_blade(self)
    }

    pub fn into_odd(self) -> Odd<T, N> where T:AllocOdd<N> {
        Odd::from_blade(self)
    }

    pub fn into_multivector(self) -> Multivector<T, N> where T:AllocMultivector<N> {
        Multivector::from_blade(self)
    }

}

impl<T:AllocEven<N>+Zero, N:Dim> Even<T,N> {

    // pub(crate) fn grade_index(&self, g:usize) -> usize {
    //     grade_index_in_versor(self.dim(), g)
    // }

    pub fn grade_select_generic<G:Dim>(self, g:G) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        let n = self.dim_generic();
        if g.value()%2 == 0 {
            Blade::from_iter_generic(
                n, g, self.into_iter().skip(grade_index_in_versor(n.value(),g.value()))
            )
        } else {
            Blade::zeroed_generic(n, g)
        }
    }

    pub fn grade_select_dyn(self, g:usize) -> Blade<T,N,Dynamic> where T:AllocBlade<N,Dynamic> {
        self.grade_select_generic(Dynamic::new(g))
    }

    pub fn grade_select<G:DimName>(self) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        self.grade_select_generic(G::name())
    }

    pub fn into_multivector(self) -> Multivector<T,N> where T:AllocMultivector<N> {
        Multivector::from_even(self)
    }

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_versor(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
        )
    }

}

impl<T:AllocOdd<N>+Zero, N:Dim> Odd<T,N> {

    // pub(crate) fn grade_index(&self, g:usize) -> usize {
    //     grade_index_in_versor(self.dim(), g)
    // }

    pub fn grade_select_generic<G:Dim>(self, g:G) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        let n = self.dim_generic();
        if g.value()%2 == 1 {
            Blade::from_iter_generic(
                n, g, self.into_iter().skip(grade_index_in_versor(n.value(),g.value()))
            )
        } else {
            Blade::zeroed_generic(n, g)
        }
    }

    pub fn grade_select_dyn(self, g:usize) -> Blade<T,N,Dynamic> where T:AllocBlade<N,Dynamic> {
        self.grade_select_generic(Dynamic::new(g))
    }

    pub fn grade_select<G:DimName>(self) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        self.grade_select_generic(G::name())
    }

    pub fn into_multivector(self) -> Multivector<T,N> where T:AllocMultivector<N> {
        Multivector::from_odd(self)
    }

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_versor(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
        )
    }

}

#[inline(always)]
fn grade_index(n:usize) -> impl Iterator<Item=(usize, usize)> {
    (0..=n).flat_map(
        move |g| (0..binom(n, g)).map(move |i| (g, i))
    )
}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {

    // pub(crate) fn grade_index(&self, g:usize) -> usize {
    //     grade_index_in_multivector(self.dim(), g)
    // }

    pub fn grade_select_generic<G:Dim>(self, g:G) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        let n = self.dim_generic();
        Blade::from_iter_generic(
            n, g, self.into_iter().skip(grade_index_in_multivector(n.value(),g.value()))
        )
    }

    pub fn grade_select_dyn(self, g:usize) -> Blade<T,N,Dynamic> where T:AllocBlade<N,Dynamic> {
        self.grade_select_generic(Dynamic::new(g))
    }

    pub fn grade_select<G:DimName>(self) -> Blade<T,N,G> where T:AllocBlade<N,G> {
        self.grade_select_generic(G::name())
    }

    pub fn select_even(self) -> Even<T,N> where T:AllocEven<N> {
        let n = self.dim_generic();
        Even::from_iter_generic(n,
            self.into_iter().zip(grade_index(n.value())).filter_map(
                |(x,(g, _))| if g&1 == 0 { Some(x) } else { None }
            )
        )
    }

    pub fn select_odd(self) -> Odd<T,N> where T:AllocOdd<N> {
        let n = self.dim_generic();
        Odd::from_iter_generic(n,
            self.into_iter().zip(grade_index(n.value())).filter_map(
                |(x, (g, _))| if g&1 != 0 { Some(x) } else { None }
            )
        )
    }

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_multivector(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
        )
    }

    pub fn from_even(x: Even<T,N>) -> Self where T:AllocEven<N>+Zero {
        let n = x.dim_generic();
        let mut iter = x.into_iter();
        Self::from_iter_generic(n,
            grade_index(n.value()).map(
                |(g, _)|
                if g&1 == 0 {
                    iter.next().unwrap()
                } else {
                    T::zero()
                }
            )
        )
    }

    pub fn from_odd(x: Odd<T,N>) -> Self where T:AllocOdd<N>+Zero {
        let n = x.dim_generic();
        let mut iter = x.into_iter();
        Self::from_iter_generic(n,
            (0..=n.value()).flat_map(
                |g| (0..binom(n.value(), g)).map(move |i| (g, i))
            ).map(
                |(g, _)|
                if g&1 != 0 {
                    iter.next().unwrap()
                } else {
                    T::zero()
                }
            )
        )
    }

}

impl<T:AllocEven<N>+AllocBlade<N,G>+Zero, N:Dim, G:DimEven> From<Blade<T,N,G>> for Even<T,N> {
    fn from(b: Blade<T,N,G>) -> Even<T,N> { Self::from_blade(b) }
}

impl<T:AllocOdd<N>+AllocBlade<N,G>+Zero, N:Dim, G:DimOdd> From<Blade<T,N,G>> for Odd<T,N> {
    fn from(b: Blade<T,N,G>) -> Odd<T,N> { Self::from_blade(b) }
}

impl<T:AllocMultivector<N>+AllocBlade<N,G>+Zero, N:Dim, G:Dim> From<Blade<T,N,G>> for Multivector<T,N> {
    fn from(b: Blade<T,N,G>) -> Multivector<T,N> { Self::from_blade(b) }
}

impl<T:AllocMultivector<N>+AllocEven<N>+Zero, N:Dim> From<Even<T,N>> for Multivector<T,N> {
    fn from(b: Even<T,N>) -> Multivector<T,N> { Self::from_even(b) }
}

impl<T:AllocMultivector<N>+AllocOdd<N>+Zero, N:Dim> From<Odd<T,N>> for Multivector<T,N> {
    fn from(b: Odd<T,N>) -> Multivector<T,N> { Self::from_odd(b) }
}
