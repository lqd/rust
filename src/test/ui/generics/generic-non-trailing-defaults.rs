struct Heap;

struct Vec<A = Heap, T>(A, T);
//~^ ERROR type parameters must be declared prior to defaulted parameters

struct Foo<A, B = Vec<C>, C>(A, B, C);
//~^ ERROR type parameters must be declared prior to defaulted parameters
//~| ERROR type parameters with a default cannot use forward declared identifiers

fn main() {}
