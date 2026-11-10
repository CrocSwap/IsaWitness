import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0195
import ArmFull.Fn.M0202
import ArmFull.Fn.M1126
import ArmFull.Fn.M1127
import ArmFull.Fn.M1128

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

def decode_LDNF1D_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 64
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_LDNF1D_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
  | 256 =>
    (do
      (execute_LDNF1D_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
  | 512 =>
    (do
      (execute_LDNF1D_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
  | 1024 =>
    (do
      (execute_LDNF1D_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
  | 2048 =>
    (do
      (execute_LDNF1D_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
  | _ => (pure (()))


def decode_STR_P_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Pt : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Pt)
  let n : Int := (BitVec.toNat Rn)
  let imm : Int := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 =>
    (do
      (execute_STR_P_BI__ 128 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STR_P_BI__ 256 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STR_P_BI__ 512 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STR_P_BI__ 1024 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STR_P_BI__ 2048 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STR_Z_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let imm : Int := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 =>
    (do
      (execute_STR_Z_BI__ 128 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STR_Z_BI__ 256 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STR_Z_BI__ 512 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STR_Z_BI__ 1024 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STR_Z_BI__ 2048 imm (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_FMOPA_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPS_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPA_ZA_PP_ZZ_64 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF64F64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPS_ZA_PP_ZZ_64 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF64F64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_BFMOPA_ZA32_PP_ZZ__ (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMOPA_ZA32_PP_ZZ__ 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BFMOPA_ZA32_PP_ZZ__ 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BFMOPA_ZA32_PP_ZZ__ 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BFMOPA_ZA32_PP_ZZ__ 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BFMOPA_ZA32_PP_ZZ__ 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_BFMOPS_ZA32_PP_ZZ__ (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMOPS_ZA32_PP_ZZ__ 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BFMOPS_ZA32_PP_ZZ__ 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BFMOPS_ZA32_PP_ZZ__ 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BFMOPS_ZA32_PP_ZZ__ 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BFMOPS_ZA32_PP_ZZ__ 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPA_ZA32_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMOPA_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPA_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPA_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPA_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPA_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPS_ZA32_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMOPS_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPS_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPS_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPS_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPS_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_LDR_ZA_RI__ (Rv : (BitVec 2)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let v : Int := (BitVec.toNat (0b011#3 +++ Rv))
  let offset : Int := (BitVec.toNat off4)
  match SVL with
  | 128 =>
    (do
      (execute_LDR_ZA_RI__ 128 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_LDR_ZA_RI__ 256 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_LDR_ZA_RI__ 512 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_LDR_ZA_RI__ 1024 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_LDR_ZA_RI__ 2048 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_STR_ZA_RI__ (Rv : (BitVec 2)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let v : Int := (BitVec.toNat (0b011#3 +++ Rv))
  let offset : Int := (BitVec.toNat off4)
  match SVL with
  | 128 =>
    (do
      (execute_STR_ZA_RI__ 128 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_STR_ZA_RI__ 256 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_STR_ZA_RI__ 512 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_STR_ZA_RI__ 1024 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_STR_ZA_RI__ 2048 (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FADD_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEF64F64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_FADD_ZA_ZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FADD_ZA_ZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FADD_ZA_ZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FADD_ZA_ZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FADD_ZA_ZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FSUB_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEF64F64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_FSUB_ZA_ZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FSUB_ZA_ZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FSUB_ZA_ZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FSUB_ZA_ZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FSUB_ZA_ZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
