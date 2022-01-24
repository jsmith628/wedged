
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
/// # use wedged::base::binom;
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

    //LUTs for the win!
    //yes, yes, I should probably do this programmatically, but it was fun and I wanted to type it all out
    const LUT: [[usize; 16]; 16] = [
        [1, 0,    0,   0,   0,     0,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 1,    0,   0,   0,     0,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 2,    1,   0,   0,     0,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 3,    3,   1,   0,     0,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 4,    6,   4,   1,     0,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 5,   10,  10,   5,     1,    0,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 6,   15,  20,  15,     6,    1,    0,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 7,   21,  35,  35,    21,    7,    1,    0,    0,    0,    0,   0,   0,  0, 0],
        [1, 8,   28,  56,  70,    56,   28,    8,    1,    0,    0,    0,   0,   0,  0, 0],
        [1, 9,   36,  84,  126,  126,   84,   36,    9,    1,    0,    0,   0,   0,  0, 0],
        [1, 10,  45, 120,  210,  252,  210,  120,   45,   10,    1,    0,   0,   0,  0, 0],
        [1, 11,  55, 165,  330,  462,  462,  330,  165,   55,   11,    1,   0,   0,  0, 0],
        [1, 12,  66, 220,  495,  792,  924,  792,  495,  220,   66,   12,   1,   0,  0, 0],
        [1, 13,  78, 286,  715, 1287, 1716, 1716, 1287,  715,  286,   78,  13,   1,  0, 0],
        [1, 14,  91, 364, 1001, 2002, 3003, 3432, 3003, 2002, 1001,  364,  91,  14,  1, 0],
        [1, 15, 105, 455, 1365, 3003, 5005, 6435, 6435, 5005, 3003, 1365, 455, 105, 15, 1],
    ];

    //should make some stuff run a little faster
    if n<16 && k<16 { return LUT[n][k]; }

    //base cases
    if k>n { return 0; }
    if k==0 { return 1; }

    //Note that we are guaranteed that this division has no remainder specifically because we
    //compute the numerator and denominator in this order
    (n-k+1) * binom(n, k-1) / k
}

/// The number of elements in the even subalgebra of the given dimension
/// This is equivalent to `2^(n-1)`, except for `n==1` where it returns `1`
pub const fn even_elements(n:usize) -> usize {
    if n==0 { 1 } else { 1 << (n-1) /*2^(n-1)*/ }
}

/// The number of elements in the odd components of dimension `n`.
/// This is equivalent to `2^(n-1)`, except for `n==0` where it returns `0`
pub const fn odd_elements(n:usize) -> usize {
    if n==0 { 0 } else { 1 << (n-1) /*2^(n-1)*/ }
}

/// The number of elements in the clifford algebra of dimension `n`.
/// This is equivalent to `2^n` for all `n`
pub const fn multivector_elements(n:usize) -> usize {
    1 << n
}

///Computes the index of the first grade `g` element in a versor of dimension `n`
pub const fn grade_index_in_versor(n:usize, g:usize) -> usize {
    if g<=1 { return 0; }
    binom(n, g-2) + grade_index_in_versor(n, g-2)
}

///Computes the index of the first grade `g` element in a multivector of dimension `n`
pub const fn grade_index_in_multivector(n:usize, g:usize) -> usize {
    if g==0 { return 0; }
    binom(n, g-1) + grade_index_in_multivector(n, g-1)
}

///
/// Iterates over the number of elements of each blade in the given dimension
///
/// # Examples
/// ```
/// # use wedged::base::components_of;
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
pub fn components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
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
/// # use wedged::base::even_components_of;
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
pub fn even_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).step_by(2)
}

///
/// Iterates over the number of elements of each _odd_ blade in the given dimension
///
/// # Examples
/// ```
/// # use wedged::base::odd_components_of;
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
pub fn odd_components_of(n: usize) -> impl std::iter::Iterator<Item=usize> {
    components_of(n).skip(1).step_by(2)
}

#[cfg(test)]
mod tests {

    use super::*;

    const fn direct_binom(n: usize, k: usize) -> usize {
        if k>n { return 0; }
        if k==0 { return 1; }
        (n-k+1) * direct_binom(n, k-1) / k
    }

    //wanna make sure I did the math right on the LUT
    #[test]
    fn test_lut() {
        for n in 0..=16 {
            for k in 0..=16 {
                assert_eq!(binom(n,k), direct_binom(n,k));
            }
        }
    }

}
