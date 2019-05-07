// This test is validating a difference between AST borrowck
// and MIR borrowck that is "fixed by NLL". This test encodes
// that NLL mode and Polonius mode make this compile-fail, but
// also that this NLL error is turned into a warning in the default
// NLL-migrate mode.
// The polonius compare-mode runs with the full NLL mode, not the 
// NLL-migrate mode. We cannot currently encode a test that is
// run-pass or compile-fail based on compare-mode and nll-mode.
// So just ignore it instead:

// ignore-compare-mode-polonius

// compile-pass
#![allow(unused)]

fn f() {
    let mut x: Box<()> = Box::new(());

    || {
        &mut x
    };
}


fn main() {}
