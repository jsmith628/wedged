
use super::*;

#[inline(always)]
fn project_blade<T,N:Dim,G1:Dim,G2:Dim>(b1: &Blade<T,N,G1>, b2: Blade<T,N,G2>) -> Blade<T,N,G2> where
    G2: DimSymSub<G1>,
    // DimSymDiff<G2,G1>: DimSymSub<G1, Output=G2>,
    T: AllocBlade<N,G1> + AllocBlade<N,G2> + AllocBlade<N,DimSymDiff<G2,G1>> + RefRing
{
    let (n1, n2, g1, g2) = (b1.dim_generic(), b2.dim_generic(), b1.grade_generic(), b2.grade_generic());

    if n1!=n2 { panic!("Dimension mismatch when projecting blades: {}!={}", n1.value(), n2.value()) }

    //if b has a higher grade, projecting all its basis to a lower space will result in an end value of zero
    if g2.value() > g1.value() {
        return Blade::zeroed_generic(n2, g2);
    }

    //Unfortunately, in order to prevent theb1.norm_sqrd() trait bounds from getting unwieldly, we have
    //to use Dynamic dimensions and grades. Once specialization is stabilized, we can fix this.
    //As for now... this is unfortunately a bit slower than doing things statically, but the
    //benchmarks don't seem to show it *much* slower
    // mul_selected::<_,_,Blade<_,_,_>>(
    //     mul_selected::<_,_,Blade<_,_,_>>(
    //         b2, b1, (Dynamic::new(n1.value()), Dynamic::new(g1.value()-g2.value()))
    //     ),
    //     b1,
    //     (n2, g2)
    // )

    //we use mul_selected for the second % operation so we don't have to have a
    //trait bound on DimSymDiff<G2,G1> since we already know what the result should be
    //Now... we *could* just drop into Dynamic dims here, but that's a little too slow
    mul_selected(b2 % b1, b1, (n2, g2))

}

pub trait Project<B> {
    type Output;
    fn project(&self, b:B) -> Self::Output;
}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<Blade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = Blade<T,N,G2>;

    fn project(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> {
        let factor = if self.grade()&0b10 != 0 { -self.norm_sqrd() } else { self.norm_sqrd() };
        project_blade(self.as_inner(), b) / factor
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<SimpleBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        SimpleBlade::from_inner_unchecked(Project::project(self, b.into_inner()))
    }

}



impl<T, N:Dim, G1:Dim, G2:Dim> Project<UnitBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        SimpleBlade::from_inner_unchecked(Project::project(self, b.into_inner()))
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<Blade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = Blade<T,N,G2>;

    fn project(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> {
        let proj = project_blade(self.as_inner(), b);
        if self.grade()&0b10 != 0 { -proj } else { proj }
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<SimpleBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        SimpleBlade::from_inner_unchecked(Project::project(self, b.into_inner()))
    }

}



impl<T, N:Dim, G1:Dim, G2:Dim> Project<UnitBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefComplexField
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        SimpleBlade::from_inner_unchecked(Project::project(self, b.into_inner()))
    }

}


impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {

    pub fn normalize(self) -> UnitBlade<T,N,G> where T: RefComplexField
    {
        UnitBlade::from_inner_unchecked(self.data.normalize())
    }

    pub fn norm_and_normalize(self) -> (T, UnitBlade<T,N,G>) where T: RefComplexField
    {
        let (l, b) = self.data.norm_and_normalize();
        (l, UnitBlade::from_inner_unchecked(b))
    }

    #[inline(always)]
    pub fn project<B>(&self, b: B) -> <Self as Project<B>>::Output where Self: Project<B>
    {
        Project::project(self, b)
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {

    pub fn as_simple_blade(self) -> SimpleBlade<T,N,G> {
        SimpleBlade::from_inner_unchecked(self.into_inner())
    }

    #[inline(always)]
    pub fn project<B>(&self, b: B) -> <Self as Project<B>>::Output where Self: Project<B>
    {
        Project::project(self, b)
    }

}

// #[cfg(tests)]
// mod tests {
//
//     use super::*;
//
//     const N: usize = TEST_DIM;
//
//     #[test]
//     fn vector_basis() {
//
//         for 0..N {
//
//         }
//
//     }
//
// }

#[test]
fn project() {

    use crate::algebra::*;

    let x = SimpleVec3::new(1.0, 0.0, 0.0);
    let y = SimpleVec3::new(1.0, 1.0, 0.0);

    assert_eq!(x.project(y), SimpleVec3::new(1.0, 0.0, 0.0));
    assert_eq!(y.project(x), SimpleVec3::new(0.5, 0.5, 0.0));

    let plane = SimpleBiVec3::new(0.0, 1.0, 0.0);

    assert_eq!(plane.project(x), SimpleVec3::new(1.0, 0.0, 0.0));
    assert_eq!(plane.project(y), SimpleVec3::new(1.0, 0.0, 0.0));

}


#[cfg(test)]
mod benches {

    use super::*;
    use test::black_box;
    use test::Bencher;


    #[bench]
    fn project_method(b: &mut Bencher) {
        b.iter(
            || for _ in 0..1000 {
                let x = black_box(SimpleVec3::new(1.0, 0.0, 0.0));
                let p = black_box(SimpleBiVec3::new(0.0f64, 1.0, 0.0));
                black_box(p.project(x));
            }
        )
    }

    #[bench]
    fn project_explicit(b: &mut Bencher) {
        b.iter(
            || for _ in 0..1000 {
                let x = black_box(SimpleVec3::new(1.0, 0.0, 0.0));
                let p = black_box(SimpleBiVec3::new(0.0f64, 1.0, 0.0));
                black_box(((x % &p) % &p) / -p.norm_sqrd());
            }
        )
    }
}
