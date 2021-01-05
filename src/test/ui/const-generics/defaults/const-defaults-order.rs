// This test checks the diagnostics and ordering of various combinations of const generics defaults
// with other kinds of generic parameters used with and without bounds, with and without default
// values.

// revisions: min full
#![cfg_attr(full, feature(const_generics))]
#![cfg_attr(full, allow(incomplete_features))]
#![crate_type = "lib"]

// Under `min_const_generics`, the correct ordering is: lifetimes, then types, then consts, then
// defaulted parameters (both types and consts, with a default value). Additionally, no defaulted
// parameter can be used together with a const parameter.

// An example of good ordering, with incompatibilities: defaulted types used together with defaulted
// consts.
struct GoodOrdering<
    'a,
    'b: 'a,
    T,
    U: 'b,
    V = u8,
    W: 'b = i8,

    const O: usize = 0,
    //~^ ERROR default values for const generic parameters are experimental
    //[min]~^^ ERROR using type defaults and const parameters in the same parameter list

    const P: usize = 1
    //~^ ERROR default values for const generic parameters are experimental
    //[min]~^^ ERROR using type defaults and const parameters in the same parameter list
>(
    &'a (),
    &'b (),
    [T; O],
    [U; P],
    [V; O],
    [W; P],
);

// An example of bad ordering for every kind of parameter, with incompatibilities: defaulted types
// used together with defaulted consts.
struct BadOrdering<
    'a,
    T,
    const N: usize,

    V = u8,
    //[min]~^ ERROR using type defaults and const parameters in the same parameter list

    const O: usize = 0,
    //~^ ERROR default values for const generic parameters are experimental
    //[min]~^^ ERROR using type defaults and const parameters in the same parameter list

    'b: 'a,
    //~^ ERROR lifetime parameters must be declared prior to defaulted parameters

    W: 'b = i8,
    //[min]~^ ERROR using type defaults and const parameters in the same parameter list

    U: 'b,
    //~^ ERROR type parameters must be declared prior to defaulted parameters

    const P: usize = 1,
    //~^ ERROR default values for const generic parameters are experimental
    //[min]~^^ ERROR using type defaults and const parameters in the same parameter list

    const M: usize,
    //~^ ERROR const parameters must be declared prior to defaulted parameters
    //[min]~^^ ERROR using type defaults and const parameters in the same parameter list
>(
    &'a (),
    &'b (),
    [T; N],
    [U; M],
    [V; O],
    [W; P],
);
