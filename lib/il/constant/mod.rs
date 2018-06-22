//! A `Constant` holds a single value.

use il::*;
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use std::fmt;
use std::ops::*;

mod constant_biguint;
mod constant_u64;

use self::constant_biguint::ConstantBigUint;
use self::constant_u64::ConstantU64;


/// A constant value for Falcon IL
///
/// IL Constants in Falcon are backed by both rust's `u64` primitive, and
/// `BigUint` from the `num-bigint` crate. This allows modelling and simulation
/// of instructions which must operate on values >64 bits in size. When a
/// Constant has 64 or less bits, the `u64` will be used, incurring minimal
/// performance overhead.
///
/// The Falcon IL Expression operations are provided as methods over `Constant`.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub enum Constant {
    U64(ConstantU64),
    BigUint(ConstantBigUint)
}


impl Constant {
    /// Create a new `Constant` with the given value and bitness.
    pub fn new(value: u64, bits: usize) -> Constant {
        if bits > 64 {
            Constant::BigUint(ConstantBigUint::new(value, bits))
        }
        else {
            Constant::U64(ConstantU64::new(value, bits))
        }
    }

    /// Create a new `Constant` from the given `BigUint`.
    pub fn new_big(value: BigUint, bits: usize) -> Constant {
        Constant::BigUint(ConstantBigUint::new_big(value, bits))
    }

    /// Crates a constant from a decimal string of the value
    pub fn from_decimal_string(s: &String, bits: usize) -> Result<Constant> {
        let c = ConstantBigUint::from_decimal_string(s, bits)?;

        Ok(if bits <= 64 {
            Constant::U64(ConstantU64::new(c.value_u64().unwrap(), bits))
        }
        else {
            Constant::BigUint(c)
        })
    }

    /// Get the value of this `Constant` if it is a `u64`.
    pub fn value_u64(&self) -> Option<u64> {
        match self {
            Constant::U64(c) => Some(c.value()),
            Constant::BigUint(c) => c.value_u64()
        }
    }

    /// Get the value of this `Constant` as a `BigUint`.
    pub fn value_biguint(&self) -> BigUint {
        match self {
            Constant::U64(c) => BigUint::from_u64(c.value()).unwrap(),
            Constant::BigUint(c) => c.value().clone()
        }
    }

    /// Get the number of bits for this `Constant`.
    pub fn bits(&self) -> usize {
        match self {
            Constant::U64(c) => c.bits(),
            Constant::BigUint(c) => c.bits()
        }
    }

    /// Returns true if the value in this Constant is 0, false otherwise.
    pub fn is_zero(&self) -> bool {
        match self {
            Constant::U64(c) => c.is_zero(),
            Constant::BigUint(c) => c.is_zero()
        }
    }

    /// Returns true if the value in this constant is 1, false otherwise.
    pub fn is_one(&self) -> bool {
        match self {
            Constant::U64(c) => c.is_one(),
            Constant::BigUint(c) => c.is_one()
        }
    }


    fn binop<FB, FU>(lhs: &Constant, rhs: &Constant, fb: FB, fu: FU)
        -> Result<Constant>
        where FB: Fn(&ConstantBigUint, &ConstantBigUint)
                -> Result<ConstantBigUint>,
              FU: Fn(&ConstantU64, &ConstantU64) -> Result<ConstantU64> {

        Ok(match lhs {
            Constant::U64(lhs) => Constant::U64(match rhs {
                Constant::U64(rhs) => fu(lhs, rhs)?,
                Constant::BigUint(rhs) => {
                    let rhs: ConstantU64 =
                        rhs.value_u64()
                            .map(|v| ConstantU64::new(v, lhs.bits()))
                            .ok_or(ErrorKind::Sort)?;
                    fu(lhs, &rhs)?
                }
            }),
            Constant::BigUint(lhs) => Constant::BigUint(match rhs {
                Constant::U64(rhs) =>
                    fb(lhs, &ConstantBigUint::new(rhs.value(), rhs.bits()))?,
                Constant::BigUint(rhs) =>
                    fb(lhs, rhs)?
            })
        })
    }


    pub fn add(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.add(r), |l, r| l.add(r))
    }

    pub fn sub(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.sub(r), |l, r| l.sub(r))
    }

    pub fn mul(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.mul(r), |l, r| l.mul(r))
    }

    pub fn divu(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.divu(r), |l, r| l.divu(r))
    }

    pub fn modu(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.modu(r), |l, r| l.modu(r))
    }

    pub fn divs(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.divs(r), |l, r| l.divs(r))
    }

    pub fn mods(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.mods(r), |l, r| l.mods(r))
    }

    pub fn and(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.and(r), |l, r| l.and(r))
    }

    pub fn or(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.or(r), |l, r| l.or(r))
    }

    pub fn xor(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.xor(r), |l, r| l.xor(r))
    }

    pub fn shl(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.shl(r), |l, r| l.shl(r))
    }

    pub fn shr(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.shr(r), |l, r| l.shr(r))
    }

    pub fn cmpeq(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.cmpeq(r), |l, r| l.cmpeq(r))
    }

    pub fn cmpneq(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.cmpneq(r), |l, r| l.cmpneq(r))
    }

    pub fn cmpltu(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.cmpltu(r), |l, r| l.cmpltu(r))
    }

    pub fn cmplts(&self, rhs: &Constant) -> Result<Constant> {
        Constant::binop(self, rhs, |l, r| l.cmplts(r), |l, r| l.cmplts(r))
    }

    pub fn trun(&self, bits: usize) -> Result<Constant> {
        match self {
            Constant::U64(c) => Ok(Constant::U64(c.trun(bits)?)),
            Constant::BigUint(c) => Ok(Constant::BigUint(c.trun(bits)?))
        }
    }

    pub fn zext(&self, bits: usize) -> Result<Constant> {
        match self {
            Constant::U64(c) => Ok(Constant::U64(c.zext(bits)?)),
            Constant::BigUint(c) => Ok(Constant::BigUint(c.zext(bits)?))
        }
    }

    pub fn sext(&self, bits: usize) -> Result<Constant> {
        match self {
            Constant::U64(c) => Ok(Constant::U64(c.sext(bits)?)),
            Constant::BigUint(c) => Ok(Constant::BigUint(c.sext(bits)?))
        }
    }
}


impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::U64(c) => write!(f, "{}", c),
            Constant::BigUint(c) => write!(f, "{}", c)
        }
    }
}


impl Into<Expression> for Constant {
    fn into(self) -> Expression {
        Expression::constant(self)
    }
}


#[test]
fn constant_add() {
    assert_eq!(Constant::new(1, 64).add(&Constant::new(1, 64)).unwrap(),
               Constant::new(2, 64));
    assert_eq!(Constant::new(0xff, 8).add(&Constant::new(1, 8)).unwrap(),
               Constant::new(0, 8));
}

#[test]
fn constant_sub() {
    assert_eq!(Constant::new(1, 64).sub(&Constant::new(1, 64)).unwrap(),
               Constant::new(0, 64));
    assert_eq!(Constant::new(0, 64).sub(&Constant::new(1, 64)).unwrap(),
               Constant::new(0xffffffffffffffff, 64));
}

#[test]
fn constant_mul() {
    assert_eq!(Constant::new(6, 64).mul(&Constant::new(4, 64)).unwrap(),
               Constant::new(24, 64));
}

#[test]
fn constant_divu() {
    assert_eq!(Constant::new(6, 64).divu(&Constant::new(4, 64)).unwrap(),
               Constant::new(1, 64));
}

#[test]
fn constant_modu() {
    assert_eq!(Constant::new(6, 64).modu(&Constant::new(4, 64)).unwrap(),
               Constant::new(2, 64));
}

#[test]
fn constant_divs() {
    assert_eq!(Constant::new(6, 64).divs(&Constant::new(4, 64)).unwrap(),
               Constant::new(1, 64));
}

#[test]
fn constant_mods() {
    assert_eq!(Constant::new(6, 64).mods(&Constant::new(4, 64)).unwrap(),
               Constant::new(2, 64));
}

#[test]
fn constant_and() {
    assert_eq!(Constant::new(0xff00ff, 64).and(&Constant::new(0xf0f0f0, 64)).unwrap(),
               Constant::new(0xf000f0, 64));
}

#[test]
fn constant_or() {
    assert_eq!(Constant::new(0xff00ff, 64).or(&Constant::new(0xf0f0f0, 64)).unwrap(),
               Constant::new(0xfff0ff, 64));
}

#[test]
fn constant_xor() {
    assert_eq!(Constant::new(0xff00ff, 64).xor(&Constant::new(0xf0f0f0, 64)).unwrap(),
               Constant::new(0x0ff00f, 64));
}

#[test]
fn constant_shl() {
    assert_eq!(Constant::new(1, 64).shl(&Constant::new(8, 64)).unwrap(),
               Constant::new(0x100, 64));
}

#[test]
fn constant_shr() {
    assert_eq!(Constant::new(0x100, 64).shr(&Constant::new(8, 64)).unwrap(),
               Constant::new(1, 64));
}

#[test]
fn constant_cmpeq() {
    assert_eq!(Constant::new(1, 64).cmpeq(&Constant::new(1, 64)).unwrap(),
               Constant::new(1, 1));
    assert_eq!(Constant::new(1, 64).cmpeq(&Constant::new(2, 64)).unwrap(),
               Constant::new(0, 1));
}

#[test]
fn constant_cmpneq() {
    assert_eq!(Constant::new(1, 64).cmpneq(&Constant::new(1, 64)).unwrap(),
               Constant::new(0, 1));
    assert_eq!(Constant::new(1, 64).cmpneq(&Constant::new(2, 64)).unwrap(),
               Constant::new(1, 1));
}

#[test]
fn constant_cmpltu() {
    assert_eq!(Constant::new(1, 64).cmpltu(&Constant::new(1, 64)).unwrap(),
               Constant::new(0, 1));
    assert_eq!(Constant::new(1, 64).cmpltu(&Constant::new(2, 64)).unwrap(),
               Constant::new(1, 1));
}

#[test]
fn constant_cmplts() {
    assert_eq!(Constant::new(1, 64).cmplts(&Constant::new(1, 64)).unwrap(),
               Constant::new(0, 1));
    assert_eq!(Constant::new(1, 64).cmplts(&Constant::new(2, 64)).unwrap(),
               Constant::new(1, 1));
    assert_eq!(Constant::new(0xffffffffffffffff, 64).cmplts(&Constant::new(1, 64)).unwrap(),
               Constant::new(1, 1));
}