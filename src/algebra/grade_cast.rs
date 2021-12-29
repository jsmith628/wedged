use super::*;

impl<T:AllocEven<N>+Zero, N:Dim> Even<T,N> {

    pub(crate) fn grade_index(&self, g:usize) -> usize {
        grade_index_in_versor(self.dim(), g)
    }

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

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_versor(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
        )
    }

}

impl<T:AllocOdd<N>+Zero, N:Dim> Odd<T,N> {

    pub(crate) fn grade_index(&self, g:usize) -> usize {
        grade_index_in_versor(self.dim(), g)
    }

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

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_versor(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
        )
    }

}

impl<T:AllocMultivector<N>, N:Dim> Multivector<T,N> {

    pub(crate) fn grade_index(&self, g:usize) -> usize {
        grade_index_in_multivector(self.dim(), g)
    }

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

    pub fn from_blade<G:Dim>(b: Blade<T,N,G>) -> Self where T:AllocBlade<N,G>+Zero {
        Self::from_iter_generic(
            b.dim_generic(),
            (0..grade_index_in_multivector(b.dim(), b.grade()))
            .map(|_| T::zero()).chain(b).chain(repeat_with(|| T::zero()))
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
