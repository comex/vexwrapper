#![allow(non_upper_case_globals, dead_code)]
#![feature(associated_consts)]
extern crate libvex_sys;
//use libvex_sys::IcoConsts::*;
//use libvex_sys::IexConsts::*;
use libvex_sys::IopConsts::*;
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Signedness {
    Signed,
    Unsigned,
}
pub use Signedness::{Signed, Unsigned};
fn signed_if(x: bool) -> Signedness {
    if x { Signed } else { Unsigned }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct U128 {
    pub lo: u64,
    pub hi: u64,
}
impl U128 {
    const ZERO: U128 = U128 { lo: 0, hi: 0 };
    fn from(lo: u64) -> U128 { U128 { lo: lo, hi: 0 } }
}
impl From<u64> for U128 {
    fn from(lo: u64) -> U128 {
        U128 { lo: lo, hi: 0 }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    WideningMul(Signedness),
    Div(Signedness),
    Mod(Signedness),

    Or,
    And,
    Xor,
    Shl,
    Shr,
    Sar,
    CmpEq,
    CmpNe,
    CmpLt(Signedness),
    CmpLe(Signedness),
    CmpGt(Signedness),
    CmpGe(Signedness),
    Max(Signedness),

    FCmp,

    // simd
    SatAdd(Signedness),
    SatSub(Signedness),
    HalfAdd(Signedness),
    HalfSub(Signedness),
    SumAbsoluteDifferences(Signedness),

    Unsupported(u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Unop {
    Not,
    Neg,
    Clz,
    Ctz,
    FUpcast(Ty),
    FNeg,
    FAbs,
    Bitcast(Ty),

    // Less important
    FTrunc64As32,
    FToISimd(Signedness),
    IToFSimd(Signedness),
}


#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RoundedUnop {
    FDowncast(Ty),
    FSqrt,
    FToI(Signedness, Ty),
    IToF(Signedness, Ty),
    Round,

    // Less important stuff after here
    // Trig
    Sin,
    Cos,
    Tan,
    TwoXMinus1,

    // PPC
    Rsqrte,

}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RoundedBinop {
    FAdd,
    FSub,
    FMul,
    FDiv,

    // Less important stuff after here
    Atan,

    // x86 shit
    Yl2x,
    Yl2xp1,
    PRem,
    PRemC3210,
    PRem1,
    PRem1C3210,
    Scale,

}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RoundedTriop {
    FMA,
    FMS,
}

pub type Lanes = u8;

pub enum Expr<Ref> {
    Bin(Binop, Ref, Ref),
    Un(Unop, Ref),
    RoundedUn(RoundedUnop, Ref, Ref),
    RoundedBin(RoundedBinop, Ref, Ref, Ref),
    RoundedTri(RoundedTriop, Ref, Ref, Ref, Ref),
    SimdUn(Lanes, Unop, Ref),
    SimdBin(Lanes, Binop, Ref, Ref),
    ITE(Ref, Ref, Ref),
    Ext(Signedness, Ty, Ref),
    Trunc(Ty, Ref),
    ConstInt(Ty, U128),
}

impl<Ref> Expr<Ref> {
    fn is_const_zero(&self) -> bool {
        if let &Expr::ConstInt(_, U128::ZERO) = self { true } else { false }
    }
}

pub struct TExpr<Ref> {
    pub ty: Ty,
    pub ex: Expr<Ref>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
    F32,
    F64,
    F128,
}
pub use Ty::*;

impl Ty {
    fn is_int(self) -> bool {
        match self {
            I1 | I8 | I16 | I32 | I64 | I128 => true,
            _ => false
        }
    }
    fn is_float(self) -> bool {
        match self {
            F32 | F64 | F128 => true,
            _ => false
        }
    }
    fn same_size_i2f(self) -> Option<Ty> {
        match self {
            I32 =>  Some(F32),
            I64 =>  Some(F64),
            I128 => Some(F128),
            _ => None,
        }
    }
    fn same_size_f2i(self) -> Option<Ty> {
        match self {
            F32 =>  Some(I32),
            F64 =>  Some(I64),
            F128 => Some(I128),
            _ => None,
        }
    }
    fn max_int_val(self) -> Option<U128> {
        match self {
            I1 =>  Some(1.into()),
            I8 =>  Some((std::u8::MAX as u64).into()),
            I16 => Some((std::u16::MAX as u64).into()),
            I32 => Some((std::u32::MAX as u64).into()),
            I64 => Some(std::u64::MAX.into()),
            I128 => Some(U128 { lo: std::u64::MAX, hi: std::u64::MAX }),
            _ => None
        }
    }
    fn double_int(self) -> Option<Ty> {
        match self {
            I8 =>  Some(I16),
            I16 => Some(I32),
            I32 => Some(I64),
            I64 => Some(I128),
            _ => None
        }
    }
}

fn guess_type<B: Builder>(b: &B, ex: Expr<B::Ref>) -> Ty {
    match &ex {
        &Expr::Bin(op, ref left, ref right) => {
            let left = b.get(left);
            let right = b.get(right);
            let lty = left.ty;
            let rty = right.ty;
            match op {
                Binop::Shl | Binop::Shr | Binop::Sar => {
                    assert!(rty.is_int());
                    return lty;
                },
                _ => assert_eq!(lty, rty),
            }
            match op {
                Binop::WideningMul(_) => lty.double_int().unwrap(),
                Binop::CmpEq | Binop::CmpNe | Binop::CmpLt(_) |
                Binop::CmpLe(_) | Binop::CmpGt(_) | Binop::CmpGe(_) => I1,
                Binop::FCmp => I32,
                _ => lty
            }
        },
        &Expr::Un(op, ref arg) => {
            let arg = b.get(arg);
            let ty = arg.ty;
            match op {
                Unop::Clz | Unop::Ctz => I32,
                Unop::FUpcast(uty) => {
                    assert!(ty != uty);
                    uty
                },
                _ => ty
            }
        },
        &Expr::RoundedUn(op, ref rm, ref arg) => {
            let rm = b.get(rm);
            let arg = b.get(arg);
            assert_eq!(rm.ty, I32); // rounding mode
            let ty = arg.ty;
            assert!(ty.is_float());
            match op {
                RoundedUnop::FDowncast(lty) => {
                    assert!(lty != ty);
                    lty
                },
                RoundedUnop::FSqrt => ty,
                RoundedUnop::FToI(_, toty) => {
                    assert!(toty.is_int());
                    toty
                },
                RoundedUnop::IToF(_, toty) => {
                    assert!(toty.is_float());
                    toty
                },
                _ => ty,
            }
        },
        &Expr::RoundedBin(op, ref rm, ref l, ref r) => {
            let rm = b.get(rm);
            let l = b.get(l);
            let r = b.get(r);
            assert_eq!(rm.ty, I32); // rounding mode
            assert_eq!(l.ty, r.ty);
            assert!(l.ty.is_float());
            let ty = r.ty;
            match op {
                _ => ty
            }
        },
        &Expr::RoundedTri(_op, ref rm, ref x, ref y, ref z) => {
            let rm = b.get(rm);
            let x = b.get(x);
            let y = b.get(y);
            let z = b.get(z);
            assert_eq!(rm.ty, I32);
            let ty = x.ty;
            assert_eq!(ty, y.ty);
            assert_eq!(ty, z.ty);
            assert!(ty.is_float());
            ty
        },
        &Expr::SimdUn(_lanes, _op, ref x) => {
            // TODO
            let x = b.get(x);
            x.ty
        },
        &Expr::SimdBin(_lanes, _op, ref l, ref r) => {
            // TODO
            let l = b.get(l);
            let r = b.get(r);
            assert_eq!(l.ty, r.ty);
            l.ty
        },
        &Expr::ITE(ref iff, ref then, ref els) => {
            let iff = b.get(iff);
            let then = b.get(then);
            let els = b.get(els);
            assert_eq!(iff.ty, I1);
            assert_eq!(then.ty, els.ty);
            then.ty
        },
        &Expr::Ext(_, ty, ref x) => {
            assert!(b.get(x).ty.max_int_val().unwrap() > ty.max_int_val().unwrap());
            ty
        },
        &Expr::Trunc(ty, ref x) => {
            assert!(b.get(x).ty.max_int_val().unwrap() < ty.max_int_val().unwrap());
            ty
        },
        &Expr::ConstInt(ty, num) => {
            assert!(num <= ty.max_int_val().expect("ConstInt ty not int"));
            ty
        },
    }
}

trait RefTy : Clone {}

trait Builder {
    type Ref: RefTy;
    fn get(&self, r: &Self::Ref) -> &TExpr<Self::Ref>;
    fn build(&self, Expr<Self::Ref>) -> Self::Ref;
    fn bin(&self, op: Binop, left: Self::Ref, right: Self::Ref) -> Self::Ref {
        let xleft = self.get(&left);
        let xright = self.get(&right);
        match op {
            Binop::Add | Binop::Or | Binop::Xor => {
                if xleft.ex.is_const_zero() { return right; }
                if xright.ex.is_const_zero() { return left; }
            },
            Binop::Sub => {
                if xright.ex.is_const_zero() { return left; }
            },
            _ => ()
        }
        // xxx constant fold
        self.build(Expr::Bin(op, left, right))
    }
    fn un(&self, op: Unop, arg: Self::Ref) -> Self::Ref {
        match op {
            Unop::FUpcast(ty) => {
                if ty == self.get(&arg).ty { return arg; }
            }
            _ => ()
        }
        self.build(Expr::Un(op, arg))
    }
    fn run(&self, op: RoundedUnop, rm: Self::Ref, x: Self::Ref) -> Self::Ref {
        match op {
            RoundedUnop::FDowncast(ty) => {
                if ty == self.get(&x).ty { return x; }
            }
            _ => ()
        }
        self.build(Expr::RoundedUn(op, rm, x))
    }
    fn rbin(&self, op: RoundedBinop, rm: Self::Ref, l: Self::Ref, r: Self::Ref) -> Self::Ref {
        self.build(Expr::RoundedBin(op, rm, l, r))
    }
    fn rtri(&self, op: RoundedTriop, rm: Self::Ref, x: Self::Ref, y: Self::Ref, z: Self::Ref) -> Self::Ref {
        self.build(Expr::RoundedTri(op, rm, x, y, z))
    }

    fn simd_un(&self, lanes: Lanes, op: Unop, x: Self::Ref) -> Self::Ref {
        self.build(Expr::SimdUn(lanes, op, x))
    }
    fn simd_bin(&self, lanes: Lanes, op: Binop, l: Self::Ref, r: Self::Ref) -> Self::Ref {
        self.build(Expr::SimdBin(lanes, op, l, r))
    }
    /*
    fn tri(&self, op: Triop, x: Self::Ref, y: Self::Ref, z: Self::Ref) -> Self::Ref {
        self.build(Expr::Tri(op, x, y, z))
    }
    */
    fn ite(&self, iff: Self::Ref, then: Self::Ref, els: Self::Ref) -> Self::Ref {
        self.build(Expr::ITE(iff, then, els))
    }
    fn ext(&self, s: Signedness, ty: Ty, x: Self::Ref) -> Self::Ref {
        if ty == self.get(&x).ty {
            x
        } else {
            self.build(Expr::Ext(s, ty, x))
        }
    }
    fn trunc(&self, ty: Ty, x: Self::Ref) -> Self::Ref {
        if ty == self.get(&x).ty {
            x
        } else {
            self.build(Expr::Trunc(ty, x))
        }
    }
    fn const_int<N: Into<U128>>(&self, ty: Ty, num: N) -> Self::Ref {
        self.build(Expr::ConstInt(ty, num.into()))
    }
}

fn pair<B: Builder>(b: &B, mut hi: B::Ref, mut lo: B::Ref) -> B::Ref {
    let mut hty = b.get(&hi).ty;
    let lty = b.get(&lo).ty;
    assert_eq!(hty, lty);
    let int_equiv = hty.same_size_f2i();
    if let Some(ie) = int_equiv { 
        hi = b.un(Unop::Bitcast(ie), hi);
        lo = b.un(Unop::Bitcast(ie), lo);
        hty = ie;
    }
    let big = hty.double_int().unwrap();
    let mut ret = b.bin(Binop::Or,
                        b.bin(Binop::Shl, b.ext(Unsigned, big, hi), b.const_int(I32, 32)),
                        b.ext(Unsigned, big, lo));
    if let Some(_) = int_equiv {
        ret = b.un(Unop::Bitcast(big.same_size_i2f().unwrap()), ret);
    }
    ret
}

fn make_unex<B: Builder>(b: B, op: u32, x: B::Ref) -> B::Ref {
    let ty = b.get(&x).ty;
    let ppc_round = |rm: u64, x: B::Ref| {
        b.run(RoundedUnop::Round, b.const_int(I32, rm), x)
    };
    if let Some((lanes, unop)) = translate_simd_unop(op) { return b.simd_un(lanes, unop, x); }
    match op {
        Iop_Left8 | Iop_Left16 | Iop_Left32 | Iop_Left64 =>
            b.bin(Binop::Or, x.clone(), b.un(Unop::Neg, x.clone())),
        Iop_CmpNEZ8 | Iop_CmpNEZ16 | Iop_CmpNEZ32 | Iop_CmpNEZ64 =>
            b.bin(Binop::CmpNe, x, b.const_int(ty, U128::ZERO)),
        Iop_CmpwNEZ32 | Iop_CmpwNEZ64 =>
            b.ext(Signed, I64, b.bin(Binop::CmpNe, x, b.const_int(ty, U128::ZERO))),
        Iop_8Uto16 => b.ext(Unsigned, I16, x),
        Iop_8Uto32 | Iop_16Uto32 => b.ext(Unsigned, I32, x),
        Iop_8Uto64 | Iop_16Uto64 | Iop_32Uto64 => b.ext(Unsigned, I64, x),
        Iop_8Sto16 => b.ext(Signed, I16, x),
        Iop_8Sto32 | Iop_16Sto32 => b.ext(Signed, I32, x),
        Iop_8Sto64 | Iop_16Sto64 | Iop_32Sto64 => b.ext(Signed, I64, x),
        Iop_64to8 | Iop_32to8 | Iop_16to8 => b.trunc(I8, x),
        Iop_32to16 => b.trunc(I16, x),
        Iop_64to32 => b.trunc(I32, x),
        Iop_128to64 => b.trunc(I64, x),

        Iop_32HIto16 =>  b.trunc(I16,  b.bin(Binop::Shr, x, b.const_int(I32, 16))),
        Iop_64HIto32 =>  b.trunc(I32,  b.bin(Binop::Shr, x, b.const_int(I32, 32))),
        Iop_128HIto64 => b.trunc(I64, b.bin(Binop::Shr, x, b.const_int(I32, 64))),
        Iop_32to1 | Iop_64to1 => b.trunc(I1, x),

        Iop_1Uto8 =>  b.ext(Unsigned, I8, x),
        //Iop_1Uto16 => lolwat doesn't exist?
        Iop_1Uto32 => b.ext(Unsigned, I32, x),
        Iop_1Uto64 => b.ext(Unsigned, I64, x),

        Iop_1Sto8 =>  b.ext(Signed, I8, x),
        Iop_1Sto16 => b.ext(Signed, I16, x),
        Iop_1Sto32 => b.ext(Signed, I32, x),
        Iop_1Sto64 => b.ext(Signed, I64, x),

        Iop_F128HItoF64 => b.un(Unop::Bitcast(F64),
                                b.trunc(I64, b.bin(Binop::Shr, b.un(Unop::Bitcast(I128), x),
                                                               b.const_int(I32, 64)))),
        Iop_F128LOtoF64 => b.un(Unop::Bitcast(F64), b.trunc(I64, b.un(Unop::Bitcast(I128), x))),

        Iop_RoundF64toF64_NEAREST => ppc_round(0b00, x),
        Iop_RoundF64toF64_NegINF  => ppc_round(0b01, x),
        Iop_RoundF64toF64_PosINF  => ppc_round(0b10, x),
        Iop_RoundF64toF64_ZERO    => ppc_round(0b11, x),

        Iop_CmpNEZ16x2 => b.simd_bin(2, Binop::CmpNe, x, b.const_int(ty, 0)),
        Iop_CmpNEZ8x4  => b.simd_bin(4, Binop::CmpNe, x, b.const_int(ty, 0)),

        _ => b.un(translate_unop(op), x),
    }
}

fn make_binex<B: Builder>(b: &B, op: u32, l: B::Ref, r: B::Ref) -> B::Ref {
    let cmp_ord = |l: B::Ref, r: B::Ref, sign: Signedness| {
        let ty = b.get(&l).ty;
        b.ite(b.bin(Binop::CmpLt(sign), l.clone(), r.clone()),
              b.const_int(ty, 8),
              b.ite(b.bin(Binop::CmpGt(sign), l.clone(), r.clone()),
                    b.const_int(ty, 4),
                    b.const_int(ty, 2)))
    };
    if let Some(runop) = translate_runop(op) { return b.run(runop, l, r); }
    if let Some((lanes, binop)) = translate_simd_binop(op) { return b.simd_bin(lanes, binop, l, r); }

    match op {
        Iop_CmpORD32U | Iop_CmpORD64U => cmp_ord(l, r, Unsigned),
        Iop_CmpORD32S | Iop_CmpORD64S => cmp_ord(l, r, Signed),
        Iop_DivU32E | Iop_DivS32E |
        Iop_DivU64E | Iop_DivS64E => {
            let big = b.get(&l).ty.double_int().unwrap();
            b.bin(Binop::Div(signed_if(op == Iop_DivS32E || op == Iop_DivS64E)),
                  b.bin(Binop::Shl, b.ext(Unsigned, big, l), b.const_int(I32, 32)),
                  b.ext(Unsigned, big, r))
        },
        Iop_DivModU64to32 | Iop_DivModS64to32 |
        Iop_DivModS64to64 |
        Iop_DivModU128to64 | Iop_DivModS128to64 => {
            let s = signed_if(op == Iop_DivModS64to32 ||
                              op == Iop_DivModS64to64 ||
                              op == Iop_DivModS128to64);
            let r = b.ext(s, b.get(&l).ty, r);
            pair(b, b.bin(Binop::Mod(s), l.clone(), r.clone()),
                    b.bin(Binop::Div(s), l.clone(), r.clone()))
        },
        Iop_16HLto32 | Iop_32HLto64 | Iop_64HLto128 | Iop_F64HLtoF128 => pair(b, l, r),

        Iop_RoundF64toF32 => b.un(Unop::FUpcast(F64), b.run(RoundedUnop::FDowncast(F32), l, r)),

        _ => b.bin(translate_binop(op), l, r),
    }
}


fn translate_runop(x: u32) -> Option<RoundedUnop> {
    Some(match x {
        Iop_SqrtF128 | Iop_SqrtF64 | Iop_SqrtF32 => RoundedUnop::FSqrt,
        Iop_F64toI16S => RoundedUnop::FToI(Signed, I16),
        Iop_F128toI32S | Iop_F64toI32S | Iop_F32toI32S => RoundedUnop::FToI(Signed, I32),
        Iop_F128toI64S | Iop_F64toI64S | Iop_F32toI64S => RoundedUnop::FToI(Signed, I64),
        Iop_F128toI32U | Iop_F64toI32U | Iop_F32toI32U => RoundedUnop::FToI(Unsigned, I32),
        Iop_F128toI64U | Iop_F64toI64U | Iop_F32toI64U => RoundedUnop::FToI(Unsigned, I64),

        Iop_I32StoF32 | Iop_I64StoF32 =>   RoundedUnop::IToF(Signed, F32),
        Iop_I32StoF128 | Iop_I64StoF128 => RoundedUnop::IToF(Signed, F128),
        Iop_I32UtoF128 | Iop_I64UtoF128 => RoundedUnop::IToF(Unsigned, F128),
        Iop_F128toF32 | Iop_F64toF32 => RoundedUnop::FDowncast(F32),
        Iop_F128toF64 => RoundedUnop::FDowncast(F64),

        Iop_SinF64 => RoundedUnop::Sin,
        Iop_CosF64 => RoundedUnop::Cos,
        Iop_TanF64 => RoundedUnop::Tan,
        Iop_2xm1F64 => RoundedUnop::TwoXMinus1,
        Iop_RoundF64toInt | Iop_RoundF32toInt => RoundedUnop::Round,

        Iop_RSqrtEst5GoodF64 => RoundedUnop::Rsqrte,

        _ => return None,
    })
}

fn translate_simd_binop(x: u32) -> Option<(Lanes, Binop)> {
    Some(match x {
        Iop_Add16x2 => (2, Binop::Add),
        Iop_Sub16x2 => (2, Binop::Sub),
        Iop_QAdd16Sx2 => (2, Binop::SatAdd(Signed)),
        Iop_QSub16Sx2 => (2, Binop::SatSub(Signed)),
        Iop_QAdd16Ux2 => (2, Binop::SatAdd(Unsigned)),
        Iop_QSub16Ux2 => (2, Binop::SatSub(Unsigned)),

        Iop_HAdd16Sx2 => (2, Binop::HalfAdd(Signed)),
        Iop_HSub16Sx2 => (2, Binop::HalfAdd(Signed)),
        Iop_HAdd16Ux2 => (2, Binop::HalfAdd(Unsigned)),
        Iop_HSub16Ux2 => (2, Binop::HalfAdd(Unsigned)),

        Iop_Add8x4 => (4, Binop::Add),
        Iop_Sub8x4 => (4, Binop::Sub),
        Iop_QAdd8Sx4 => (4, Binop::SatAdd(Signed)),
        Iop_QSub8Sx4 => (4, Binop::SatSub(Signed)),
        Iop_QAdd8Ux4 => (4, Binop::SatAdd(Unsigned)),
        Iop_QSub8Ux4 => (4, Binop::SatSub(Unsigned)),

        Iop_HAdd8Sx4 => (4, Binop::HalfAdd(Signed)),
        Iop_HSub8Sx4 => (4, Binop::HalfAdd(Signed)),
        Iop_HAdd8Ux4 => (4, Binop::HalfAdd(Unsigned)),
        Iop_HSub8Ux4 => (4, Binop::HalfAdd(Unsigned)),

        Iop_Sad8Ux4 => (4, Binop::SumAbsoluteDifferences(Unsigned)),

        _ => return None,
    })
}

fn translate_binop(x: u32) -> Binop {
    match x {
        Iop_Add8 | Iop_Add16 | Iop_Add32 | Iop_Add64 => Binop::Add,
        Iop_Sub8 | Iop_Sub16 | Iop_Sub32 | Iop_Sub64 => Binop::Sub,
        Iop_Mul8 | Iop_Mul16 | Iop_Mul32 | Iop_Mul64 => Binop::Mul,
        Iop_Or8  | Iop_Or16  | Iop_Or32  | Iop_Or64  => Binop::Or,
        Iop_And8 | Iop_And16 | Iop_And32 | Iop_And64 => Binop::And,
        Iop_Xor8 | Iop_Xor16 | Iop_Xor32 | Iop_Xor64 => Binop::Xor,
        Iop_Shl8 | Iop_Shl16 | Iop_Shl32 | Iop_Shl64 => Binop::Shl,
        Iop_Shr8 | Iop_Shr16 | Iop_Shr32 | Iop_Shr64 => Binop::Shr,
        Iop_Sar8 | Iop_Sar16 | Iop_Sar32 | Iop_Sar64 => Binop::Sar,
        Iop_CmpEQ8 | Iop_CmpEQ16 | Iop_CmpEQ32 | Iop_CmpEQ64 => Binop::CmpEq,
        Iop_CmpNE8 | Iop_CmpNE16 | Iop_CmpNE32 | Iop_CmpNE64 => Binop::CmpNe,

        Iop_CasCmpEQ8 | Iop_CasCmpEQ16 | Iop_CasCmpEQ32 | Iop_CasCmpEQ64 => Binop::CmpEq,
        Iop_CasCmpNE8 | Iop_CasCmpNE16 | Iop_CasCmpNE32 | Iop_CasCmpNE64 => Binop::CmpNe,
        Iop_ExpCmpNE8 | Iop_ExpCmpNE16 | Iop_ExpCmpNE32 | Iop_ExpCmpNE64 => Binop::CmpNe,

        Iop_MullS8 | Iop_MullS16 | Iop_MullS32 | Iop_MullS64 => Binop::WideningMul(Signed),
        Iop_MullU8 | Iop_MullU16 | Iop_MullU32 | Iop_MullU64 => Binop::WideningMul(Unsigned),

        Iop_CmpLT32S | Iop_CmpLT64S => Binop::CmpLt(Signed),
        Iop_CmpLE32S | Iop_CmpLE64S => Binop::CmpLe(Signed),
        Iop_CmpLT32U | Iop_CmpLT64U => Binop::CmpLt(Unsigned),
        Iop_CmpLE32U | Iop_CmpLE64U => Binop::CmpLe(Unsigned),

        Iop_Max32U => Binop::Max(Unsigned),

        Iop_DivU32 | Iop_DivU64 => Binop::Div(Unsigned),
        Iop_DivS32 | Iop_DivS64 => Binop::Div(Signed),

        Iop_CmpF32 | Iop_CmpF64 | Iop_CmpF128 => Binop::FCmp,

        Iop_QAdd32S => Binop::SatAdd(Signed),
        Iop_QSub32S => Binop::SatSub(Signed),

        _ => panic!("unexpected binop {}", x),
    }
}

fn translate_simd_unop(x: u32) -> Option<(Lanes, Unop)> {
    Some(match x {
        Iop_I32UtoFx2 => (2, Unop::IToFSimd(Unsigned)),
        Iop_I32StoFx2 => (2, Unop::IToFSimd(Signed)),

        _ => return None,
    })
}

fn translate_unop(x: u32) -> Unop {
    match x {
        Iop_Not1 | Iop_Not8 | Iop_Not16 | Iop_Not32 | Iop_Not64 => Unop::Not,
        Iop_Clz64 | Iop_Clz32 => Unop::Clz,
        Iop_Ctz64 | Iop_Ctz32 => Unop::Ctz,
        Iop_NegF128 | Iop_NegF64 | Iop_NegF32 => Unop::FNeg,
        Iop_AbsF128 | Iop_AbsF64 | Iop_AbsF32 => Unop::FAbs,
        Iop_F32toF64 => Unop::FUpcast(F64),
        Iop_ReinterpF64asI64 => Unop::Bitcast(I64),
        Iop_ReinterpI64asF64 => Unop::Bitcast(F64),
        Iop_ReinterpF32asI32 => Unop::Bitcast(I32),
        Iop_ReinterpI32asF32 => Unop::Bitcast(F32),

        Iop_TruncF64asF32 => Unop::FTrunc64As32,

        _ => panic!("unexpected unop {}", x),
    }
}

fn make_triex<B: Builder>(b: &B, op: u32, x: B::Ref, y: B::Ref, z: B::Ref) -> B::Ref {
    let roundabout = |bop: RoundedBinop, rm: B::Ref, l: B::Ref, r: B::Ref| {
        b.un(Unop::FUpcast(F64),
             b.rbin(bop, rm.clone(),
                    b.run(RoundedUnop::FDowncast(F32), rm.clone(), l),
                    b.run(RoundedUnop::FDowncast(F32), rm.clone(), r)))

    };
    match op {
        Iop_AddF64r32 => roundabout(RoundedBinop::FAdd, x, y, z),
        Iop_SubF64r32 => roundabout(RoundedBinop::FSub, x, y, z),
        Iop_MulF64r32 => roundabout(RoundedBinop::FMul, x, y, z),
        Iop_DivF64r32 => roundabout(RoundedBinop::FDiv, x, y, z),

        _ => b.rbin(translate_rbinop(op), x, y, z),
    }
}

fn translate_rbinop(x: u32) -> RoundedBinop {
    match x {
        Iop_AddF128 | Iop_AddF64 | Iop_AddF32 => RoundedBinop::FAdd,
        Iop_SubF128 | Iop_SubF64 | Iop_SubF32 => RoundedBinop::FSub,
        Iop_MulF128 | Iop_MulF64 | Iop_MulF32 => RoundedBinop::FMul,
        Iop_DivF128 | Iop_DivF64 | Iop_DivF32 => RoundedBinop::FDiv,

        Iop_AtanF64 => RoundedBinop::Atan,
        Iop_Yl2xF64 => RoundedBinop::Yl2x,
        Iop_Yl2xp1F64 => RoundedBinop::Yl2xp1,
        Iop_PRemF64 => RoundedBinop::PRem,
        Iop_PRemC3210F64 => RoundedBinop::PRemC3210,
        Iop_PRem1F64 => RoundedBinop::PRem1,
        Iop_PRem1C3210F64 => RoundedBinop::PRem1C3210,
        Iop_ScaleF64 => RoundedBinop::Scale,


        _ => panic!("unexpected triop {}", x),
    }
}

fn make_qex<B: Builder>(b: &B, op: u32, w: B::Ref, x: B::Ref, y: B::Ref, z: B::Ref) -> B::Ref {
    match op {
        Iop_MAddF32 | Iop_MAddF64 | Iop_MAddF64r32 => b.rtri(RoundedTriop::FMA, w, x, y, z),
        Iop_MSubF32 | Iop_MSubF64 | Iop_MSubF64r32 => b.rtri(RoundedTriop::FMS, w, x, y, z),

        _ => panic!("unexpected qop {}", op),
    }
}

