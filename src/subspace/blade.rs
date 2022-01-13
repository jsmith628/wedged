
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

#[inline(always)]
fn reject_blade<T,N:Dim,G1:Dim,G2:Dim>(b1: &Blade<T,N,G1>, b2: Blade<T,N,G2>) -> Blade<T,N,G2> where
    G2: DimAdd<G1>,
    T: AllocBlade<N,G1> + AllocBlade<N,G2> + AllocBlade<N,DimSum<G2,G1>> + RefRing
{
    let (n1, n2, g2) = (b1.dim_generic(), b2.dim_generic(), b2.grade_generic());
    if n1!=n2 { panic!("Dimension mismatch when rejecting blades: {}!={}", n1.value(), n2.value()) }
    mul_selected(b2 ^ b1, b1, (n2, g2))
}

macro_rules! factor {
    ($b:ident) => { if $b.neg_sig() { -$b.norm_sqrd() } else { $b.norm_sqrd() } };
}

///
/// Trait for finding the parallel component of a blade `B` onto `Self`
///
/// Used primarily to drive [`Blade::project()`], [`SimpleBlade::project()`],
/// and [`UnitBlade::project()`]
///
pub trait Project<B> {
    type Output;
    fn project(&self, b:B) -> Self::Output;
}

///
/// Trait for finding the perpendicular component of a blade `B` onto `Self`
///
/// Used primarily to drive [`Blade::reject()`], [`SimpleBlade::reject()`],
/// and [`UnitBlade::reject()`]
///
pub trait Reject<B> {
    type Output;
    fn reject(&self, b:B) -> Self::Output;
}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<Blade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;
    fn project(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> { project_blade(self, b) / factor!(self) }
}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<Blade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;
    fn reject(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> { reject_blade(self, b) / factor!(self) }
}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<SimpleBlade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;
    #[inline(always)]
    fn project(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into()
    }
}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<SimpleBlade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;
    #[inline(always)]
    fn reject(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into()
    }
}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<UnitBlade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<UnitBlade<T,N,G2>> for Blade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocSimpleBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn reject(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<Blade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;
    fn project(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> { project_blade(self.as_inner(), b) / factor!(self)}
}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<Blade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;
    fn reject(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> { reject_blade(self.as_inner(), b) / factor!(self)}
}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<SimpleBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<SimpleBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn reject(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<UnitBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<UnitBlade<T,N,G2>> for SimpleBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn reject(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<Blade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;

    fn project(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> {
        let proj = project_blade(self.as_inner(), b);
        if self.neg_sig() { -proj } else { proj }
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<Blade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = Blade<T,N,G2>;

    fn reject(&self, b:Blade<T,N,G2>) -> Blade<T,N,G2> {
        let proj = reject_blade(self.as_inner(), b);
        if self.neg_sig() { -proj } else { proj }
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<SimpleBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<SimpleBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn reject(&self, b:SimpleBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Project<UnitBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimSymSub<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSymDiff<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn project(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Project::project(self, b.into_inner()).into_simple_unchecked()
    }

}

impl<T, N:Dim, G1:Dim, G2:Dim> Reject<UnitBlade<T,N,G2>> for UnitBlade<T,N,G1> where
    G2:DimAdd<G1>,
    T:AllocBlade<N,G1>+AllocBlade<N,G2>+AllocBlade<N,DimSum<G2,G1>>+RefDivRing
{
    type Output = SimpleBlade<T,N,G2>;

    #[inline(always)]
    fn reject(&self, b:UnitBlade<T,N,G2>) -> SimpleBlade<T,N,G2> {
        Reject::reject(self, b.into_inner()).into_simple_unchecked()
    }

}

macro_rules! proj_doc { () => { "Finds the parallel component of `b` onto `self`" } }
macro_rules! rej_doc { () => { "Finds the perpendicular component of `b` onto `self`" } }

impl<T:AllocSimpleBlade<N,G>, N:Dim, G:Dim> Blade<T,N,G> {

    #[doc = proj_doc!()]
    #[inline(always)]
    pub fn project<B>(&self, b: B) -> <Self as Project<B>>::Output where Self: Project<B>
    {
        Project::project(self, b)
    }

    #[doc = rej_doc!()]
    #[inline(always)]
    pub fn reject<B>(&self, b: B) -> <Self as Reject<B>>::Output where Self: Reject<B>
    {
        Reject::reject(self, b)
    }
}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> SimpleBlade<T,N,G> {

    /// Divides `self` by its norm
    pub fn normalize(self) -> UnitBlade<T,N,G> where T: RefRealField
    {
        self.data.normalize().into_unit_unchecked()
    }

    /// Divides `self` by its norm if it is non-zero
    pub fn try_normalize(self) -> Option<UnitBlade<T,N,G>> where T: RefRealField {
        self.data.try_normalize().map(|b| b.into_unit_unchecked())
    }

    /// Normalizes `self` and returns its norm and its normalization
    pub fn norm_and_normalize(self) -> (T, UnitBlade<T,N,G>) where T: RefRealField
    {
        let (l, b) = self.data.norm_and_normalize();
        (l, b.into_unit_unchecked())
    }

    /// Normalizes `self` and returns its norm and its normalization if the norm is non-zero
    pub fn try_norm_and_normalize(self) -> Option<(T, UnitBlade<T,N,G>)> where T: RefRealField
    {
        match self.data.try_norm_and_normalize() {
            Some((l,b)) => Some((l, b.into_unit_unchecked())),
            None => None
        }
    }

    #[doc = proj_doc!()]
    #[inline(always)]
    pub fn project<B>(&self, b: B) -> <Self as Project<B>>::Output where Self: Project<B>
    {
        Project::project(self, b)
    }

    #[doc = rej_doc!()]
    #[inline(always)]
    pub fn reject<B>(&self, b: B) -> <Self as Reject<B>>::Output where Self: Reject<B>
    {
        Reject::reject(self, b)
    }

}

impl<T:AllocBlade<N,G>, N:Dim, G:Dim> UnitBlade<T,N,G> {

    #[doc = proj_doc!()]
    #[inline(always)]
    pub fn project<B>(&self, b: B) -> <Self as Project<B>>::Output where Self: Project<B>
    {
        Project::project(self, b)
    }

    #[inline(always)]
    pub fn reject<B>(&self, b: B) -> <Self as Reject<B>>::Output where Self: Reject<B>
    {
        Reject::reject(self, b)
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

#[cfg(tests)]
mod tests {

    use super::*;

    #[test]
    fn project() {

        let x = SimpleVec3::new(1.0, 0.0, 0.0);
        let y = SimpleVec3::new(1.0, 1.0, 0.0);

        assert_eq!(x.project(y), SimpleVec3::new(1.0, 0.0, 0.0));
        assert_eq!(y.project(x), SimpleVec3::new(0.5, 0.5, 0.0));

        let plane = SimpleBiVec3::new(0.0, 1.0, 0.0);

        assert_eq!(plane.project(x), SimpleVec3::new(1.0, 0.0, 0.0));
        assert_eq!(plane.project(y), SimpleVec3::new(1.0, 0.0, 0.0));

    }

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
