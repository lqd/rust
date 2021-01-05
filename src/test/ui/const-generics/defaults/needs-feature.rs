//[full] run-pass
// Verifies that having generic parameters after constants is not permitted without the
// `const_generics` feature.
// revisions: min full

#![cfg_attr(full, feature(const_generics))]
#![cfg_attr(full, allow(incomplete_features))]

struct A<const N: usize, T = u32>(T);
//[min]~^ ERROR using type defaults and const parameters in the same parameter list

fn main() {
    let _: A<3> = A(0);
}
