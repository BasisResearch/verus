use vstd::prelude::*;

verus! {

pub fn double(x: u16) -> (z: u32)
    ensures z == x * 2,
{
    x as u32 + x as u32
}

pub struct Counter {
    pub n: u32,
}

pub trait Bump {
    fn bump(&mut self)
        requires old(self).n() < 100,
        ensures final(self).n() == old(self).n() + 1;

    spec fn n(&self) -> u32;
}

impl Bump for Counter {
    fn bump(&mut self) {
        self.n = self.n + 1;
    }

    open spec fn n(&self) -> u32 {
        self.n
    }
}

/// Verified, public, and never called by the binary.
pub mod twin {
    use vstd::prelude::*;

    verus! {

    pub fn double(x: u16) -> (z: u32)
        ensures z == x * 2,
    {
        x as u32 * 2
    }

    } // verus!
}

} // verus!
