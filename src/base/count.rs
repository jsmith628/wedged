
///
/// Computes the [binomial coefficient][1] of n terms at position k.
///
/// Said differently, finds the number of combinations of k objects from a set of n things.
/// This is incredibly important for geometric algebra since this is how we compute the number of
/// bases for an n-dimensional blade of grade g.
///
/// [1]: https://en.wikipedia.org/wiki/Binomial_coefficient
///
/// # Examples
///
///```
/// # use galgebra::binom;
///
/// //The first three rows of Pascal's triangle
///
/// assert_eq!(binom(0,0), 1);
///
/// assert_eq!(binom(1,0), 1);
/// assert_eq!(binom(1,1), 1);
///
/// assert_eq!(binom(2,0), 1);
/// assert_eq!(binom(2,1), 2);
/// assert_eq!(binom(2,2), 1);
///
/// assert_eq!(binom(3,0), 1);
/// assert_eq!(binom(3,1), 3);
/// assert_eq!(binom(3,2), 3);
/// assert_eq!(binom(3,3), 1);
///
/// //we get 0 if and only if k>n:
/// for n in 0..10 {
///     for k in 0..10 {
///         assert_eq!(k>n, binom(n,k)==0);
///     }
/// }
///
///
///```
///
pub const fn binom(n:usize, k:usize) -> usize {

    //base cases
    if k>n { return 0; }
    if k==0 { return 1; }

    //Note that we are guaranteed that this division has no remainder specifically because we
    //compute the numerator and denominator in this order
    (n-k+1) * binom(n, k-1) / k
}

//TODO maybe make these private

pub const fn even_elements(n:usize) -> usize {
    if n==0 { 1 } else { 1 << (n-1) /*2^(n-1)*/ }
}

pub const fn odd_elements(n:usize) -> usize {
    if n==0 { 0 } else { 1 << (n-1) /*2^(n-1)*/ }
}

pub const fn multivector_elements(n:usize) -> usize {
    1 << n
}

pub(crate) const fn grade_index_in_versor(n:usize, g:usize) -> usize {
    if g<=1 { return 0; }
    binom(n, g-2) + grade_index_in_versor(n, g-2)
}

pub(crate) const fn grade_index_in_multivector(n:usize, g:usize) -> usize {
    if g==0 { return 0; }
    binom(n, g-1) + grade_index_in_multivector(n, g-1)
}


///
/// Iterates over the number of elements of each blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::components_of;
///
/// assert_eq!(components_of(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(components_of(1).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(components_of(2).collect::<Vec<_>>(), vec![1, 2, 1]);
/// assert_eq!(components_of(3).collect::<Vec<_>>(), vec![1, 3, 3, 1]);
/// assert_eq!(components_of(4).collect::<Vec<_>>(), vec![1, 4, 6, 4, 1]);
/// assert_eq!(components_of(5).collect::<Vec<_>>(), vec![1, 5, 10, 10, 5, 1]);
/// assert_eq!(components_of(6).collect::<Vec<_>>(), vec![1, 6, 15, 20, 15, 6, 1]);
///
/// ```
///
pub(crate) fn components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    let mut binom = 1;
    (0..=n).map(
        move |g| {
            let result = binom;
            binom *= n-g;
            binom /= g+1;
            result
        }
    )
}

///
/// Iterates over the number of elements of each _even_ blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::even_components_of;
///
/// assert_eq!(even_components_of(0).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_of(1).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(even_components_of(2).collect::<Vec<_>>(), vec![1, 1]);
/// assert_eq!(even_components_of(3).collect::<Vec<_>>(), vec![1, 3]);
/// assert_eq!(even_components_of(4).collect::<Vec<_>>(), vec![1, 6, 1]);
/// assert_eq!(even_components_of(5).collect::<Vec<_>>(), vec![1, 10, 5]);
/// assert_eq!(even_components_of(6).collect::<Vec<_>>(), vec![1, 15, 15, 1]);
///
/// ```
///
pub(crate) fn even_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).step_by(2)
}

///
/// Iterates over the number of elements of each _odd_ blade in the given dimension
///
/// # Examples
/// ```
/// # use galgebra::odd_components_of;
///
/// assert_eq!(odd_components_of(0).collect::<Vec<_>>(), vec![]);
/// assert_eq!(odd_components_of(1).collect::<Vec<_>>(), vec![1]);
/// assert_eq!(odd_components_of(2).collect::<Vec<_>>(), vec![2]);
/// assert_eq!(odd_components_of(3).collect::<Vec<_>>(), vec![3, 1]);
/// assert_eq!(odd_components_of(4).collect::<Vec<_>>(), vec![4, 4]);
/// assert_eq!(odd_components_of(5).collect::<Vec<_>>(), vec![5, 10, 1]);
/// assert_eq!(odd_components_of(6).collect::<Vec<_>>(), vec![6, 20, 6]);
///
/// ```
///
pub(crate) fn odd_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).skip(1).step_by(2)
}
