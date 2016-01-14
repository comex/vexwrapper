#![allow(non_upper_case_globals, dead_code)]
extern crate libvex_sys;
use libvex_sys::*;
use std::ops::Deref;
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Signedness {
    Signed,
    Unsigned,
}
pub use Signedness::{Signed, Unsigned};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    WideningMul(Signedness),
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
    Clz,
    Ctz,
    Max(Signedness),

    Wtf(u32),
}

pub enum Expr<Ref> {
    Bin(Binop, Ref, Ref),
    Un(Unop, Ref),
    ITE(Ref, Ref, Ref),
    ConstInt(Ty, u64),
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
    F32,
    F64,
}
pub use Ty::*;

impl Ty {
    fn max_int_val(self) -> Option<u64> {
        match self {
            I1 =>  Some(1),
            I8 =>  Some(std::u8::MAX as u64),
            I16 => Some(std::u16::MAX as u64),
            I32 => Some(std::u32::MAX as u64),
            I64 => Some(std::u64::MAX),
            _ => None
        }
    }
    fn double_int(self) -> Option<Ty> {
        match self {
            I8 =>  Some(I16),
            I16 => Some(I32),
            I32 => Some(I64),
            _ => None
        }
    }
}

fn guess_type<Ref: RefTy>(ex: Expr<Ref>) -> Ty {
    match &ex {
        &Expr::Bin(op, ref left, ref right) => {
            let lty = left.ty;
            let rty = right.ty;
            assert_eq!(lty, rty);
            match op {
                Binop::WideningMul(_) => lty.double_int().unwrap(),
                Binop::CmpEq | Binop::CmpNe | Binop::CmpLt(_) |
                Binop::CmpLe(_) | Binop::CmpGt(_) | Binop::CmpGe(_) =>
                    I1,
                _ => lty
            }
        },
        &Expr::Un(op, ref arg) => {
            let ty = arg.ty;
            match op {
                _ => ty
            }
        },
        &Expr::ITE(ref iff, ref then, ref els) => {
            assert_eq!(iff.ty, I1);
            assert_eq!(then.ty, els.ty);
            then.ty
        },
        &Expr::ConstInt(ty, num) => {
            assert!(num <= ty.max_int_val().expect("ConstInt ty not int"));
            ty
        },
    }
}

trait RefTy : Clone + Deref<Target=TExpr<Self>> {}

trait Builder {
    type Ref: RefTy;
    fn build(&self, Expr<Self::Ref>) -> Self::Ref;
    fn bin(&self, op: Binop, left: Self::Ref, right: Self::Ref) -> Self::Ref {
        self.build(Expr::Bin(op, left, right))
    }
    fn un(&self, op: Unop, arg: Self::Ref) -> Self::Ref {
        self.build(Expr::Un(op, arg))
    }
    fn ite(&self, iff: Self::Ref, then: Self::Ref, els: Self::Ref) -> Self::Ref {
        self.build(Expr::ITE(iff, then, els))
    }
    fn const_int(&self, ty: Ty, num: u64) -> Self::Ref {
        self.build(Expr::ConstInt(ty, num))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Unop {
    Not,
    Neg,
    CmpNonZero,
    Left,
}
fn make_unex<B: Builder>(b: B, op: u32, x: B::Ref) -> B::Ref {
    match op {
        Iop_Left8 | Iop_Left16 | Iop_Left32 | Iop_Left64 =>
            b.bin(Binop::Or, x.clone(), b.un(Unop::Neg, x.clone())),
        Iop_CmpNEZ8 | Iop_CmpNEZ16 | Iop_CmpNEZ32 | Iop_CmpNEZ64 => {
            let ty = x.ty;
            b.bin(Binop::CmpNe, x, b.const_int(ty, 0))
        },

        _ => b.un(translate_unop(op), x),
    }
}
fn make_binex<B: Builder>(b: B, op: u32, l: B::Ref, r: B::Ref) -> B::Ref {
    let cmp_ord = |l: B::Ref, r: B::Ref, sign: Signedness| {
        let ty = l.ty;
        b.ite(b.bin(Binop::CmpLt(sign), l.clone(), r.clone()),
              b.const_int(ty, 8),
              b.ite(b.bin(Binop::CmpGt(sign), l.clone(), r.clone()),
                    b.const_int(ty, 4),
                    b.const_int(ty, 2)))
    };
    match op {
        Iop_CmpORD32U | Iop_CmpORD64U => cmp_ord(l, r, Unsigned),
        Iop_CmpORD32S | Iop_CmpORD64S => cmp_ord(l, r, Signed),

        _ => b.bin(translate_binop(op), l, r),
    }
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

        Iop_Clz64 | Iop_Clz32 => Binop::Clz,
        Iop_Ctz64 | Iop_Ctz32 => Binop::Ctz,

        Iop_CmpLT32S | Iop_CmpLT64S => Binop::CmpLt(Signed),
        Iop_CmpLE32S | Iop_CmpLE64S => Binop::CmpLe(Signed),
        Iop_CmpLT32U | Iop_CmpLT64U => Binop::CmpLt(Unsigned),
        Iop_CmpLE32U | Iop_CmpLE64U => Binop::CmpLe(Unsigned),

        Iop_Max32U => Binop::Max(Unsigned),

        _ => panic!("unexpected binop {}", x),
    }
}

fn translate_unop(x: u32) -> Unop {
    match x {
        Iop_Not8 | Iop_Not16 | Iop_Not32 | Iop_Not64 => Unop::Not,
        Iop_CmpwNEZ32 | Iop_CmpwNEZ64 => Unop::CmpNonZero,
        _ => panic!("unexpected unop {}", x),
    }
}


