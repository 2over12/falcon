//! A `Constant` holds a single value.

use il::*;
use std::fmt;


#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ConstantU64 {
    value: u64,
    bits: usize
}


fn ensure_same_sort(lhs: &ConstantU64, rhs: &ConstantU64) -> Result<()> {
    if lhs.bits() != rhs.bits() {
        Err(ErrorKind::Sort.into())
    }
    else {
        Ok(())
    }
}


impl ConstantU64 {
    /// Create a new `Constant` with the given value and bitness.
    pub(crate) fn new(value: u64, bits: usize) -> ConstantU64 {
        let value = if bits == 64 {
            value
        }
        else {
            value & ((1u64.wrapping_shl(bits as u32)).wrapping_sub(1))
        };
        ConstantU64 {
            value: value,
            bits: bits
        }
    }

    /// Get the value of this `ConstantU64`
    pub(crate) fn value(&self) -> u64 {
        self.value
    }

    /// Get the number of bits for this `Constant`.
    pub(crate) fn bits(&self) -> usize {
        self.bits
    }

    /// Returns true if the value in this Constant is 0, false otherwise.
    pub(crate) fn is_zero(&self) -> bool {
        self.value() == 0
    }

    /// Returns true if the value in this constant is 1, false otherwise.
    pub(crate) fn is_one(&self) -> bool {
        self.value() == 1
    }

    fn to_i64(&self) -> i64 {
        if self.bits == 64 || self.value() >> (self.bits - 1) == 0 {
            self.value() as i64
        }
        else {
            let mask = (-1i64 as u64) << self.bits;
            (self.value() | mask) as i64
        }
    }

    pub(crate) fn add(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_add(rhs.value()), self.bits))
    }

    pub(crate) fn sub(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_sub(rhs.value()), self.bits))
    }

    pub(crate) fn mul(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_mul(rhs.value()), self.bits))
    }

    pub(crate) fn divu(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_div(rhs.value()), self.bits))
    }

    pub(crate) fn modu(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_rem(rhs.value()), self.bits))
    }

    pub(crate) fn divs(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new((self.to_i64().wrapping_div(rhs.to_i64())) as u64,
                            self.bits))
    }

    pub(crate) fn mods(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new((self.to_i64().wrapping_rem(rhs.to_i64())) as u64,
                            self.bits))
    }

    pub(crate) fn and(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value() & rhs.value(), self.bits))
    }

    pub(crate) fn or(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value() | rhs.value(), self.bits))
    }

    pub(crate) fn xor(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value() ^ rhs.value(), self.bits))
    }

    pub(crate) fn shl(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_shl(rhs.value() as u32),
                            self.bits))
    }

    pub(crate) fn shr(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(self.value().wrapping_shr(rhs.value() as u32),
                            self.bits))
    }

    pub(crate) fn cmpeq(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(if self.value() == rhs.value() {1} else {0}, 1))
    }

    pub(crate) fn cmpneq(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(if self.value() != rhs.value() {1} else {0}, 1))
    }

    pub(crate) fn cmpltu(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(if self.value() < rhs.value() {1} else {0}, 1))
    }

    pub(crate) fn cmplts(&self, rhs: &ConstantU64) -> Result<ConstantU64> {
        ensure_same_sort(self, rhs)?;
        Ok(ConstantU64::new(if self.to_i64() < rhs.to_i64() {1} else {0}, 1))
    }

    pub(crate) fn trun(&self, bits: usize) -> Result<ConstantU64> {
        Ok(ConstantU64::new(self.value(), bits))
    }

    pub(crate) fn zext(&self, bits: usize) -> Result<ConstantU64> {
        Ok(ConstantU64::new(self.value(), bits))
    }

    pub(crate) fn sext(&self, bits: usize) -> Result<ConstantU64> {
        Ok(ConstantU64::new(self.to_i64() as u64, bits))
    }
}


impl fmt::Display for ConstantU64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:X}:{}", self.value(), self.bits)
    }
}


#[test]
fn constant_add() {
    assert_eq!(ConstantU64::new(1, 64).add(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(2, 64));
    assert_eq!(ConstantU64::new(0xff, 8)
                .add(&ConstantU64::new(1, 8))
                .unwrap()
                .value(),
               ConstantU64::new(0, 8)
                .value());
    assert_eq!(ConstantU64::new(1, 32).add(&ConstantU64::new(1, 32)).unwrap(),
               ConstantU64::new(2, 32));
}

#[test]
fn constant_sub() {
    assert_eq!(ConstantU64::new(1, 64).sub(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(0, 64));
    assert_eq!(ConstantU64::new(0, 64).sub(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(0xffffffffffffffff, 64));
}

#[test]
fn constant_mul() {
    assert_eq!(ConstantU64::new(6, 64).mul(&ConstantU64::new(4, 64)).unwrap(),
               ConstantU64::new(24, 64));
}

#[test]
fn constant_divu() {
    assert_eq!(ConstantU64::new(6, 64).divu(&ConstantU64::new(4, 64)).unwrap(),
               ConstantU64::new(1, 64));
}

#[test]
fn constant_modu() {
    assert_eq!(ConstantU64::new(6, 64).modu(&ConstantU64::new(4, 64)).unwrap(),
               ConstantU64::new(2, 64));
}

#[test]
fn constant_divs() {
    assert_eq!(ConstantU64::new(6, 64).divs(&ConstantU64::new(4, 64)).unwrap(),
               ConstantU64::new(1, 64));
}

#[test]
fn constant_mods() {
    assert_eq!(ConstantU64::new(6, 64).mods(&ConstantU64::new(4, 64)).unwrap(),
               ConstantU64::new(2, 64));
}

#[test]
fn constant_and() {
    assert_eq!(ConstantU64::new(0xff00ff, 64).and(&ConstantU64::new(0xf0f0f0, 64)).unwrap(),
               ConstantU64::new(0xf000f0, 64));
}

#[test]
fn constant_or() {
    assert_eq!(ConstantU64::new(0xff00ff, 64).or(&ConstantU64::new(0xf0f0f0, 64)).unwrap(),
               ConstantU64::new(0xfff0ff, 64));
}

#[test]
fn constant_xor() {
    assert_eq!(ConstantU64::new(0xff00ff, 64).xor(&ConstantU64::new(0xf0f0f0, 64)).unwrap(),
               ConstantU64::new(0x0ff00f, 64));
}

#[test]
fn constant_shl() {
    assert_eq!(ConstantU64::new(1, 64).shl(&ConstantU64::new(8, 64)).unwrap(),
               ConstantU64::new(0x100, 64));
}

#[test]
fn constant_shr() {
    assert_eq!(ConstantU64::new(0x100, 64).shr(&ConstantU64::new(8, 64)).unwrap(),
               ConstantU64::new(1, 64));
}

#[test]
fn constant_cmpeq() {
    assert_eq!(ConstantU64::new(1, 64).cmpeq(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(1, 1));
    assert_eq!(ConstantU64::new(1, 64).cmpeq(&ConstantU64::new(2, 64)).unwrap(),
               ConstantU64::new(0, 1));
}

#[test]
fn constant_cmpneq() {
    assert_eq!(ConstantU64::new(1, 64).cmpneq(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(0, 1));
    assert_eq!(ConstantU64::new(1, 64).cmpneq(&ConstantU64::new(2, 64)).unwrap(),
               ConstantU64::new(1, 1));
}

#[test]
fn constant_cmpltu() {
    assert_eq!(ConstantU64::new(1, 64).cmpltu(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(0, 1));
    assert_eq!(ConstantU64::new(1, 64).cmpltu(&ConstantU64::new(2, 64)).unwrap(),
               ConstantU64::new(1, 1));
}

#[test]
fn constant_cmplts() {
    assert_eq!(ConstantU64::new(1, 64).cmplts(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(0, 1));
    assert_eq!(ConstantU64::new(1, 64).cmplts(&ConstantU64::new(2, 64)).unwrap(),
               ConstantU64::new(1, 1));
    assert_eq!(ConstantU64::new(0xffffffffffffffff, 64).cmplts(&ConstantU64::new(1, 64)).unwrap(),
               ConstantU64::new(1, 1));

    assert_eq!(ConstantU64::new(1, 32).cmplts(&ConstantU64::new(1, 32)).unwrap(),
               ConstantU64::new(0, 1));
    assert_eq!(ConstantU64::new(1, 32).cmplts(&ConstantU64::new(2, 32)).unwrap(),
               ConstantU64::new(1, 1));
    assert_eq!(ConstantU64::new(0xffffffffffffffff, 32).cmplts(&ConstantU64::new(1, 32)).unwrap(),
               ConstantU64::new(1, 1));
}