//! A `Constant` holds a single value.

use il::*;
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_traits::{FromPrimitive, ToPrimitive};
use std::fmt;
use std::ops::*;


#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ConstantBigUint {
    value: BigUint,
    bits: usize
}


impl ConstantBigUint {
    /// Create a new `Constant` with the given value and bitness.
    pub(crate) fn new(value: u64, bits: usize) -> ConstantBigUint {
        ConstantBigUint {
            value: ConstantBigUint::trim_value(BigUint::from_u64(value).unwrap(),
                                        bits),
            bits: bits
        }
    }

    /// Create a new `Constant` from the given `BigUint`.
    pub(crate) fn new_big(value: BigUint, bits: usize) -> ConstantBigUint {
        ConstantBigUint {
            value: ConstantBigUint::trim_value(value, bits),
            bits: bits
        }
    }

    /// Creates a constant from a decimal string of the value
    pub(crate) fn from_decimal_string(s: &String, bits: usize)
        -> Result<ConstantBigUint> {

        let constant = ConstantBigUint::new_big(s.parse()?, bits);
        Ok(if constant.bits() < bits {
            constant.zext(bits)?
        }
        else if constant.bits() > bits {
            constant.trun(bits)?
        }
        else {
            constant
        })
    }

    fn trim_value(value: BigUint, bits: usize) -> BigUint {
        let mask = BigUint::from_u64(1).unwrap() << bits;
        let mask = mask - BigUint::from_u64(1).unwrap();
        value & mask
    }

    /// Ugly trickery to convert BigUint to BigInt
    fn to_bigint(&self) -> BigInt {
        let sign_bit = self.value.clone() >> (self.bits - 1);
        if sign_bit == BigUint::from_u64(1).unwrap() {
            let mask = BigUint::from_i64(1).unwrap() << self.bits;
            let mask = mask - BigUint::from_i64(1).unwrap();
            let v = self.value.clone() ^ mask;
            let v = v + BigUint::from_u64(1).unwrap();
            let v = BigInt::from_i64(-1).unwrap() * v.to_bigint().unwrap();
            v
        }
        else {
            self.value.to_bigint().unwrap()
        }
    }

    /// Get the value of this `Constant` if it is a `u64`.
    pub(crate) fn value_u64(&self) -> Option<u64> {
        self.value.to_u64()
    }

    /// Get the value of this `Constant` if it is a `BigUint`.
    pub(crate) fn value(&self) -> &BigUint {
        &self.value
    }

    /// Get the number of bits for this `Constant`.
    pub(crate) fn bits(&self) -> usize {
        self.bits
    }

    /// Returns true if the value in this Constant is 0, false otherwise.
    pub(crate) fn is_zero(&self) -> bool {
        self.value_u64().map(|v| v == 0).unwrap_or(false)
    }

    /// Returns true if the value in this constant is 1, false otherwise.
    pub(crate) fn is_one(&self) -> bool {
        self.value_u64().map(|v| v == 1).unwrap_or(false)
    }

    pub(crate) fn add(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(
                self.value.clone() + rhs.value.clone(),
                self.bits))
        }
    }

    pub(crate) fn sub(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            if self.value < rhs.value {
                let lhs = self.value.clone();
                let lhs = lhs | (BigUint::from_u64(1).unwrap() << self.bits);
                Ok(ConstantBigUint::new_big(lhs - rhs.value.clone(), self.bits))
            }
            else {
                Ok(ConstantBigUint::new_big(
                    self.value.clone().sub(rhs.value.clone()),
                    self.bits))
            }
        }
    }

    pub(crate) fn mul(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() * rhs.value.clone(),
                self.bits))
        }
    }

    pub(crate) fn divu(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if rhs.is_zero() { Err(ErrorKind::DivideByZero.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() / rhs.value.clone(),
                self.bits))
        }
    }

    pub(crate) fn modu(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if rhs.is_zero() { Err(ErrorKind::DivideByZero.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() % rhs.value.clone(),
                self.bits))
        }
    }

    pub(crate) fn divs(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if rhs.is_zero() { Err(ErrorKind::DivideByZero.into()) }
        else {
            let lhs = self.to_bigint();
            let rhs = rhs.to_bigint();
            let r = lhs / rhs;
            if r >= BigInt::from_i64(0).unwrap() {
                Ok(ConstantBigUint::new_big(r.to_biguint().unwrap(), self.bits))
            }
            else {
                let mask = BigInt::from_i64(1).unwrap() << self.bits;
                let mask = mask - BigInt::from_i64(1).unwrap();
                let r = (r - BigInt::from_u64(1).unwrap()) ^ mask;
                let r = r * BigInt::from_i64(-1).unwrap();
                Ok(ConstantBigUint::new_big(r.to_biguint().unwrap(), self.bits))
            }
        }
    }

    pub(crate) fn mods(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if rhs.is_zero() { Err(ErrorKind::DivideByZero.into()) }
        else {
            let lhs = self.to_bigint();
            let rhs = rhs.to_bigint();
            let r = lhs % rhs;
            if r >= BigInt::from_i64(0).unwrap() {
                Ok(ConstantBigUint::new_big(r.to_biguint().unwrap(), self.bits))
            }
            else {
                let mask = BigInt::from_i64(1).unwrap() << self.bits;
                let mask = mask - BigInt::from_i64(1).unwrap();
                let r = (r - BigInt::from_u64(1).unwrap()) ^ mask;
                let r = r * BigInt::from_i64(-1).unwrap();
                Ok(ConstantBigUint::new_big(r.to_biguint().unwrap(), self.bits))
            }
        }
    }

    pub(crate) fn and(&self, rhs: &ConstantBigUint) -> Result<ConstantBigUint> {
        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() & rhs.value.clone(),
                self.bits))
        }
    }

    pub(crate) fn or(&self, rhs: &ConstantBigUint) -> Result<ConstantBigUint> {
        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() | rhs.value.clone(), self.bits))
        }
    }

    pub(crate) fn xor(&self, rhs: &ConstantBigUint) -> Result<ConstantBigUint> {
        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone() ^ rhs.value.clone(), self.bits))
        }
    }

    pub(crate) fn shl(&self, rhs: &ConstantBigUint) -> Result<ConstantBigUint> {
        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            let r = rhs.value
                       .to_usize().map(|bits| self.value.clone() << bits)
                       .unwrap_or(BigUint::from_u64(0).unwrap());
            Ok(ConstantBigUint::new_big(r, self.bits))
        }
    }

    pub(crate) fn shr(&self, rhs: &ConstantBigUint) -> Result<ConstantBigUint> {
        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else {
            let r = rhs.value
                       .to_usize().map(|bits| self.value.clone() >> bits)
                       .unwrap_or(BigUint::from_u64(0).unwrap());
            Ok(ConstantBigUint::new_big(r, self.bits))
        }
    }

    pub(crate) fn cmpeq(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if self.value == rhs.value {
            Ok(ConstantBigUint::new(1, 1))
        }
        else {
            Ok(ConstantBigUint::new(0, 1))
        }
    }

    pub(crate) fn cmpneq(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if self.value == rhs.value {
            Ok(ConstantBigUint::new(0, 1))
        }
        else {
            Ok(ConstantBigUint::new(1, 1))
        }
    }

    pub(crate) fn cmpltu(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { Err(ErrorKind::Sort.into()) }
        else if self.value < rhs.value {
            Ok(ConstantBigUint::new(1, 1))
        }
        else {
            Ok(ConstantBigUint::new(0, 1))
        }
    }

    pub(crate) fn cmplts(&self, rhs: &ConstantBigUint)
        -> Result<ConstantBigUint> {

        if self.bits() != rhs.bits() { return Err(ErrorKind::Sort.into()); }
        let lhs = self.to_bigint();
        let rhs = rhs.to_bigint();
        if lhs < rhs {
            Ok(ConstantBigUint::new(1, 1))
        }
        else {
            Ok(ConstantBigUint::new(0, 1))
        }
    }

    pub(crate) fn trun(&self, bits: usize) -> Result<ConstantBigUint> {
        if bits >= self.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone(), bits))
        }
    }

    pub(crate) fn zext(&self, bits: usize) -> Result<ConstantBigUint> {
        if bits <= self.bits() { Err(ErrorKind::Sort.into()) }
        else {
            Ok(ConstantBigUint::new_big(self.value.clone(), bits))
        }
    }

    pub(crate) fn sext(&self, bits: usize) -> Result<ConstantBigUint> {
        if bits <= self.bits() || bits % 8 > 0 { Err(ErrorKind::Sort.into()) }
        else {
            let sign_bit = self.value.clone() >> (self.bits - 1);
            let value = if sign_bit == BigUint::from_u64(1).unwrap() {
                let mask = BigUint::from_u64(1).unwrap() << bits;
                let mask = mask - BigUint::from_u64(1).unwrap();
                let mask = mask << self.bits;
                self.value.clone() | mask
            }
            else {
                self.value.clone()
            };
            Ok(ConstantBigUint::new_big(value, bits))
        }
    }
}


impl fmt::Display for ConstantBigUint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:X}:{}", self.value, self.bits)
    }
}


#[test]
fn constant_add() {
    assert_eq!(ConstantBigUint::new(1, 64).add(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(2, 64));
    assert_eq!(ConstantBigUint::new(0xff, 8).add(&ConstantBigUint::new(1, 8)).unwrap(),
               ConstantBigUint::new(0, 8));
}

#[test]
fn constant_sub() {
    assert_eq!(ConstantBigUint::new(1, 64).sub(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(0, 64));
    assert_eq!(ConstantBigUint::new(0, 64).sub(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(0xffffffffffffffff, 64));
}

#[test]
fn constant_mul() {
    assert_eq!(ConstantBigUint::new(6, 64).mul(&ConstantBigUint::new(4, 64)).unwrap(),
               ConstantBigUint::new(24, 64));
}

#[test]
fn constant_divu() {
    assert_eq!(ConstantBigUint::new(6, 64).divu(&ConstantBigUint::new(4, 64)).unwrap(),
               ConstantBigUint::new(1, 64));
}

#[test]
fn constant_modu() {
    assert_eq!(ConstantBigUint::new(6, 64).modu(&ConstantBigUint::new(4, 64)).unwrap(),
               ConstantBigUint::new(2, 64));
}

#[test]
fn constant_divs() {
    assert_eq!(ConstantBigUint::new(6, 64).divs(&ConstantBigUint::new(4, 64)).unwrap(),
               ConstantBigUint::new(1, 64));
}

#[test]
fn constant_mods() {
    assert_eq!(ConstantBigUint::new(6, 64).mods(&ConstantBigUint::new(4, 64)).unwrap(),
               ConstantBigUint::new(2, 64));
}

#[test]
fn constant_and() {
    assert_eq!(ConstantBigUint::new(0xff00ff, 64).and(&ConstantBigUint::new(0xf0f0f0, 64)).unwrap(),
               ConstantBigUint::new(0xf000f0, 64));
}

#[test]
fn constant_or() {
    assert_eq!(ConstantBigUint::new(0xff00ff, 64).or(&ConstantBigUint::new(0xf0f0f0, 64)).unwrap(),
               ConstantBigUint::new(0xfff0ff, 64));
}

#[test]
fn constant_xor() {
    assert_eq!(ConstantBigUint::new(0xff00ff, 64).xor(&ConstantBigUint::new(0xf0f0f0, 64)).unwrap(),
               ConstantBigUint::new(0x0ff00f, 64));
}

#[test]
fn constant_shl() {
    assert_eq!(ConstantBigUint::new(1, 64).shl(&ConstantBigUint::new(8, 64)).unwrap(),
               ConstantBigUint::new(0x100, 64));
}

#[test]
fn constant_shr() {
    assert_eq!(ConstantBigUint::new(0x100, 64).shr(&ConstantBigUint::new(8, 64)).unwrap(),
               ConstantBigUint::new(1, 64));
}

#[test]
fn constant_cmpeq() {
    assert_eq!(ConstantBigUint::new(1, 64).cmpeq(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(1, 1));
    assert_eq!(ConstantBigUint::new(1, 64).cmpeq(&ConstantBigUint::new(2, 64)).unwrap(),
               ConstantBigUint::new(0, 1));
}

#[test]
fn constant_cmpneq() {
    assert_eq!(ConstantBigUint::new(1, 64).cmpneq(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(0, 1));
    assert_eq!(ConstantBigUint::new(1, 64).cmpneq(&ConstantBigUint::new(2, 64)).unwrap(),
               ConstantBigUint::new(1, 1));
}

#[test]
fn constant_cmpltu() {
    assert_eq!(ConstantBigUint::new(1, 64).cmpltu(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(0, 1));
    assert_eq!(ConstantBigUint::new(1, 64).cmpltu(&ConstantBigUint::new(2, 64)).unwrap(),
               ConstantBigUint::new(1, 1));
}

#[test]
fn constant_cmplts() {
    assert_eq!(ConstantBigUint::new(1, 64).cmplts(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(0, 1));
    assert_eq!(ConstantBigUint::new(1, 64).cmplts(&ConstantBigUint::new(2, 64)).unwrap(),
               ConstantBigUint::new(1, 1));
    assert_eq!(ConstantBigUint::new(0xffffffffffffffff, 64).cmplts(&ConstantBigUint::new(1, 64)).unwrap(),
               ConstantBigUint::new(1, 1));
}