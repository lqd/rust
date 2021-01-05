// revisions: full min
#![cfg_attr(full, feature(const_generics))] //[full]~WARN the feature `const_generics` is incomplete

struct A<T = u32, const N: usize> {
    //[min]~^ ERROR using type defaults and const parameters in the same parameter list
    //~^^ ERROR const parameters must be declared prior to defaulted parameters
    arg: T,
}

fn main() {}
