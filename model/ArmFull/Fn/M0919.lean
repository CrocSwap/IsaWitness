import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0846
import ArmFull.Fn.M0847

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

def decode_UCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UCLAMP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_UCLAMP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_UCLAMP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_UCLAMP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_UCLAMP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_SCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SCLAMP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_SCLAMP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_SCLAMP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_SCLAMP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_SCLAMP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_UCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_UCLAMP_MZ_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_UCLAMP_MZ_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_UCLAMP_MZ_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_UCLAMP_MZ_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_UCLAMP_MZ_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_SCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_SCLAMP_MZ_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_SCLAMP_MZ_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_SCLAMP_MZ_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_SCLAMP_MZ_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_SCLAMP_MZ_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_UUNPK_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UUNPK_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UUNPK_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UUNPK_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UUNPK_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UUNPK_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SUNPK_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SUNPK_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SUNPK_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SUNPK_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SUNPK_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SUNPK_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UUNPK_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UUNPK_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UUNPK_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UUNPK_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UUNPK_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UUNPK_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SUNPK_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SUNPK_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SUNPK_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SUNPK_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SUNPK_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SUNPK_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SQRSHR_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHR_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 256 =>
    (do
      (execute_SQRSHR_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 512 =>
    (do
      (execute_SQRSHR_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 1024 =>
    (do
      (execute_SQRSHR_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 2048 =>
    (do
      (execute_SQRSHR_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | _ => (pure (()))


def decode_UQRSHR_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 =>
    (do
      (execute_UQRSHR_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 256 =>
    (do
      (execute_UQRSHR_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 512 =>
    (do
      (execute_UQRSHR_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 1024 =>
    (do
      (execute_UQRSHR_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 2048 =>
    (do
      (execute_UQRSHR_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | _ => (pure (()))


def decode_SQRSHRU_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRU_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 256 =>
    (do
      (execute_SQRSHRU_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 512 =>
    (do
      (execute_SQRSHRU_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 1024 =>
    (do
      (execute_SQRSHRU_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | 2048 =>
    (do
      (execute_SQRSHRU_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        shift))
  | _ => (pure (()))


def decode_SQRSHRN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHRN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHRN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHRN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHRN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_UQRSHRN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_UQRSHRN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_UQRSHRN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_UQRSHRN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_UQRSHRN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_UQRSHRN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_SQRSHRUN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRUN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHRUN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHRUN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHRUN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHRUN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_SQRSHR_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHR_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHR_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHR_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHR_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHR_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_UQRSHR_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_UQRSHR_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_UQRSHR_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_UQRSHR_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_UQRSHR_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_UQRSHR_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


def decode_SQRSHRU_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 => (pure (8))
    | b__0 => (pure (16)) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 =>
    (do
      (execute_SQRSHRU_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 256 =>
    (do
      (execute_SQRSHRU_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 512 =>
    (do
      (execute_SQRSHRU_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 1024 =>
    (do
      (execute_SQRSHRU_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | 2048 =>
    (do
      (execute_SQRSHRU_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) shift))
  | _ => (pure (()))


end ArmFull.Functions
