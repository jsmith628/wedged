
use super::*;

#[inline]
const fn upcast_dst_index(n:usize, dn:usize, g:usize) -> usize {
    if 2*g <= n+1 || dn==0 || g>n+1 {
        0
    } else {
        binom(n, n+1-g) + upcast_dst_index(n+1, dn-1, g)
    }
}

#[inline]
const fn downcast_src_index(n:usize, dn:usize, g:usize) -> usize {
    if n==0 || dn==0 {
        0
    } else if 2*g <= n || g>n {
        downcast_src_index(n-1, dn-1, g)
    } else {
        binom(n-1, n-g) + downcast_src_index(n-1, dn-1, g)
    }
}

#[inline]
fn cast_blade<T:Zero, B:Iterator<Item=T>>(
    b: &mut B, n1:usize, n2:usize, g:usize, e1:usize, e2:usize, dst: &mut [MaybeUninit<T>]
) {
    if n2 > n1 {
        let start = upcast_dst_index(n1, n2-n1, g);

        //any zeroes at the beginning
        for i in 0..start { dst[i] = MaybeUninit::new(T::zero()) }

        //copy the data into the right spot
        for i in 0..e1 {
            dst[i+start] = MaybeUninit::new(b.next().unwrap());
        }

        //the remaining zeroes
        for i in (start+e1)..e2 {
            dst[i] = MaybeUninit::new(T::zero())
        }
    } else {

        let start = downcast_src_index(n1, n1-n2, g);

        //skip "start" indices
        for _ in 0..start { b.next(); }

        //extract the correct number of values from b
        for i in 0..e2 {
            dst[i] = MaybeUninit::new(b.next().unwrap());
        }

        //skip the remaining amount in this blade
        for _ in (start+e2)..e1 { b.next(); }

    }
}

#[inline]
fn cast_subspace<T:Zero, B:Iterator<Item=T>, I:Iterator<Item=(usize, usize, usize)>>(
    b: &mut B, n1:usize, n2:usize, grades:I, dst: &mut [MaybeUninit<T>]
) {
    let x = b;
    let mut dst = dst;
    for (g, e1, e2) in grades {
        cast_blade(x, n1, n2, g, e1, e2, dst);
        dst = &mut dst[e2..];
    }
}

impl<T:AllocBlade<N1,G>+Zero, N1:Dim, G:Dim> Blade<T,N1,G> {

    pub fn cast_dim_generic<N2:Dim>(self, n:N2) -> Blade<T,N2,G> where T:AllocBlade<N2,G> {
        //the destination value
        let mut uninit = AllocateBlade::<T,N2,G>::uninit(n, self.grade_generic());

        //copy the right amount of values from the source to the destination at the right spot
        let (n1, n2, g, e) = (self.dim(), n.value(), self.grade(), self.elements());
        cast_blade(&mut self.into_iter(), n1, n2, g, e, uninit.elements(), uninit.borrow_mut());

        //assume init
        Blade { data: unsafe { uninit.assume_init() } }
    }

    pub fn cast_dim_dyn(self, n:usize) -> Blade<T,Dynamic,G> where T:AllocBlade<Dynamic,G> {
        self.cast_dim_generic(Dynamic::new(n))
    }

    pub fn cast_dim<N2:DimName>(self) -> Blade<T,N2,G> where T:AllocBlade<N2,G> {
        self.cast_dim_generic(N2::name())
    }

}

macro_rules! impl_dim_cast {
    ($($Ty:ident<T:$Alloc:ident,N1>, $Allocate:ident, |$n1:ident, $n2:ident| $iter:expr;)*) => {

        $(
            impl<T:$Alloc<N1>+Zero, N1:Dim> $Ty<T,N1> {

                pub fn cast_dim_generic<N2:Dim>(self, n:N2) -> $Ty<T,N2> where T:$Alloc<N2> {
                    //the destination value
                    let mut uninit = $Allocate::<T,N2>::uninit(n);

                    //copy the right amount of values from the source to the destination at the right spot
                    let ($n1, $n2) = (self.dim(), n.value());
                    cast_subspace(&mut self.into_iter(), $n1, $n2, $iter, uninit.borrow_mut());

                    //assume init
                    $Ty { data: unsafe { uninit.assume_init() } }
                }

                pub fn cast_dim_dyn(self, n:usize) -> $Ty<T,Dynamic> where T:$Alloc<Dynamic> {
                    self.cast_dim_generic(Dynamic::new(n))
                }

                pub fn cast_dim<N2:DimName>(self) -> $Ty<T,N2> where T:$Alloc<N2> {
                    self.cast_dim_generic(N2::name())
                }
            }
        )*

    }
}

impl_dim_cast!(
    Even<T:AllocEven,N1>, AllocateEven, |n1,n2| {
        components_of(n1).zip(components_of(n2)).enumerate().map(|(g,(e1,e2))| (g,e1,e2)).step_by(2)
    };

    Odd<T:AllocOdd,N1>, AllocateOdd, |n1,n2| {
        components_of(n1).zip(components_of(n2)).enumerate().map(|(g,(e1,e2))| (g,e1,e2)).skip(1).step_by(2)
    };

    Multivector<T:AllocMultivector,N1>, AllocateMultivector, |n1,n2| {
        components_of(n1).zip(components_of(n2)).enumerate().map(|(g,(e1,e2))| (g,e1,e2))
    };
);

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn upcast_downcast_idempotence() {

        for n1 in 1..=16 {
            for n2 in n1..=16 {

                for g in 0..=16 {
                    let b1 = BladeD::from_iterator(n1, g, 1..);
                    let b2 = b1.clone().cast_dim_dyn(n2).cast_dim_dyn(n1);
                    assert_eq!(b1, b2);
                }

                let m1 = EvenD::from_iterator(n1, 1..);
                let m2 = m1.clone().cast_dim_dyn(n2).cast_dim_dyn(n1);
                assert_eq!(m1, m2);

                let m1 = OddD::from_iterator(n1, 1..);
                let m2 = m1.clone().cast_dim_dyn(n2).cast_dim_dyn(n1);
                assert_eq!(m1, m2);

                let m1 = MultivectorD::from_iterator(n1, 1..);
                let m2 = m1.clone().cast_dim_dyn(n2).cast_dim_dyn(n1);
                assert_eq!(m1, m2);


            }

        }

    }


}
