import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1139
import ArmFull.Fn.M1140
import ArmFull.Fn.M1141

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

def decode_FMLS_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_FMLS_ZA_ZZi_H2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FMLS_ZA_ZZi_H2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FMLS_ZA_ZZi_H2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FMLS_ZA_ZZi_H2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FMLS_ZA_ZZi_H2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMLA_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMLA_ZA_ZZi_H2xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLA_ZA_ZZi_H2xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLA_ZA_ZZi_H2xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLA_ZA_ZZi_H2xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLA_ZA_ZZi_H2xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMLS_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMLS_ZA_ZZi_H2xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLS_ZA_ZZi_H2xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLS_ZA_ZZi_H2xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLS_ZA_ZZi_H2xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLS_ZA_ZZi_H2xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FMLA_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FMLA_ZA_ZZi_H4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FMLA_ZA_ZZi_H4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FMLA_ZA_ZZi_H4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FMLA_ZA_ZZi_H4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FMLA_ZA_ZZi_H4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FMLS_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FMLS_ZA_ZZi_H4xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FMLS_ZA_ZZi_H4xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FMLS_ZA_ZZi_H4xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FMLS_ZA_ZZi_H4xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FMLS_ZA_ZZi_H4xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMLA_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMLA_ZA_ZZi_H4xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLA_ZA_ZZi_H4xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLA_ZA_ZZi_H4xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLA_ZA_ZZi_H4xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLA_ZA_ZZi_H4xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMLS_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMLS_ZA_ZZi_H4xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLS_ZA_ZZi_H4xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLS_ZA_ZZi_H4xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLS_ZA_ZZi_H4xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLS_ZA_ZZi_H4xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset)) sub_op
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMAX_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAX_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAX_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAX_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAX_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMAX_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAX_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAX_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAX_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAX_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMIN_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMIN_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMIN_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMIN_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMIN_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMIN_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMIN_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMIN_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMIN_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMIN_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMAX_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAX_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAX_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAX_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAX_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMAX_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAX_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAX_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAX_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAX_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMIN_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMIN_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMIN_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMIN_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMIN_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMIN_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMIN_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMIN_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMIN_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMIN_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAXNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAXNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMINNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMINNM_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMINNM_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMINNM_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMINNM_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMINNM_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMINNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMINNM_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMINNM_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMINNM_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMINNM_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMINNM_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


end ArmFull.Functions
