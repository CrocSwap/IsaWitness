import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0916
import ArmFull.Fn.M0917
import ArmFull.Fn.M0921

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

def decode_UMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLSL_ZA_ZZi_1 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSL_ZA_ZZi_1 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSL_ZA_ZZi_1 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSL_ZA_ZZi_1 1024 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSL_ZA_ZZi_1 2048 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLAL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLAL_ZA_ZZi_1 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLAL_ZA_ZZi_1 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLAL_ZA_ZZi_1 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLAL_ZA_ZZi_1 1024 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLAL_ZA_ZZi_1 2048 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLSL_ZA_ZZi_1 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSL_ZA_ZZi_1 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSL_ZA_ZZi_1 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSL_ZA_ZZi_1 1024 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSL_ZA_ZZi_1 2048 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLAL_ZA_ZZi_2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLAL_ZA_ZZi_2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLAL_ZA_ZZi_2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLAL_ZA_ZZi_2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLAL_ZA_ZZi_2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLSL_ZA_ZZi_2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSL_ZA_ZZi_2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSL_ZA_ZZi_2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSL_ZA_ZZi_2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSL_ZA_ZZi_2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLAL_ZA_ZZi_2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLAL_ZA_ZZi_2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLAL_ZA_ZZi_2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLAL_ZA_ZZi_2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLAL_ZA_ZZi_2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLSL_ZA_ZZi_2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSL_ZA_ZZi_2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSL_ZA_ZZi_2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSL_ZA_ZZi_2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSL_ZA_ZZi_2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_UMLAL_ZA_ZZi_4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLAL_ZA_ZZi_4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLAL_ZA_ZZi_4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLAL_ZA_ZZi_4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLAL_ZA_ZZi_4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_UMLSL_ZA_ZZi_4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSL_ZA_ZZi_4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSL_ZA_ZZi_4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSL_ZA_ZZi_4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSL_ZA_ZZi_4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_SMLAL_ZA_ZZi_4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLAL_ZA_ZZi_4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLAL_ZA_ZZi_4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLAL_ZA_ZZi_4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLAL_ZA_ZZi_4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_SMLSL_ZA_ZZi_4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSL_ZA_ZZi_4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSL_ZA_ZZi_4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSL_ZA_ZZi_4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSL_ZA_ZZi_4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BMOPA_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
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
      (execute_BMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_BMOPS_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
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
      (execute_BMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_SMOPA_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
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
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMOPA_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 256 =>
    (do
      (execute_SMOPA_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 512 =>
    (do
      (execute_SMOPA_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 1024 =>
    (do
      (execute_SMOPA_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 2048 =>
    (do
      (execute_SMOPA_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | _ => (pure (()))


def decode_UMOPA_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
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
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMOPA_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 256 =>
    (do
      (execute_UMOPA_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 512 =>
    (do
      (execute_UMOPA_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 1024 =>
    (do
      (execute_UMOPA_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 2048 =>
    (do
      (execute_UMOPA_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
