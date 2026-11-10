import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1235
import ArmFull.Fn.M1236
import ArmFull.Fn.M1237

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

def decode_LDNT1H_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1H_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1H_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1H_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1H_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1H_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1W_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1W_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1W_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1W_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1W_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1W_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1SB_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1SH_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1B_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1B_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1B_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1B_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1B_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1B_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1H_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1H_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1H_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1H_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1H_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1H_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1W_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1W_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1W_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1W_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1W_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1W_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1D_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 64
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LDNT1D_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1D_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1D_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1D_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1D_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1SB_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LDNT1SB_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1SB_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1SB_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1SB_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1SB_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1SH_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LDNT1SH_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1SH_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1SH_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1SH_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1SH_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LDNT1SW_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 32
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LDNT1SW_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LDNT1SW_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LDNT1SW_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LDNT1SW_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LDNT1SW_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_STNT1B_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_STNT1B_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1B_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1B_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1B_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1B_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1H_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_STNT1H_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1H_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1H_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1H_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1H_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1W_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_STNT1W_Z_P_AR_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1W_Z_P_AR_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1W_Z_P_AR_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1W_Z_P_AR_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1W_Z_P_AR_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1B_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_STNT1B_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1B_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1B_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1B_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1B_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


def decode_STNT1H_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Rm)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_STNT1H_Z_P_AR_D_64_unscaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 256 =>
    (do
      (execute_STNT1H_Z_P_AR_D_64_unscaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 512 =>
    (do
      (execute_STNT1H_Z_P_AR_D_64_unscaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 1024 =>
    (do
      (execute_STNT1H_Z_P_AR_D_64_unscaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | 2048 =>
    (do
      (execute_STNT1H_Z_P_AR_D_64_unscaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (t))))
  | _ => (pure (()))


end ArmFull.Functions
