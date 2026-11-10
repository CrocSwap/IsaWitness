import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0910
import ArmFull.Fn.M0911

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

def decode_SUMLALL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLALL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZi_D 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZi_D 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZi_D 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZi_D 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZi_D 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLALL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLALL_ZA_ZZi_D 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLALL_ZA_ZZi_D 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLALL_ZA_ZZi_D 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLALL_ZA_ZZi_D 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLALL_ZA_ZZi_D 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSLL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLSLL_ZA_ZZi_D 128 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSLL_ZA_ZZi_D 256 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSLL_ZA_ZZi_D 512 esize (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSLL_ZA_ZZi_D 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSLL_ZA_ZZi_D 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLALL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLALL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLALL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLALL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLALL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSLL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLSLL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSLL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSLL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSLL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSLL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_USMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_USMLALL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_USMLALL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_USMLALL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_USMLALL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_USMLALL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SUMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i4h +++ i4l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUMLALL_ZA_ZZi_S2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLALL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZi_D2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZi_D2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZi_D2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZi_D2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZi_D2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZi_D2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLALL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         (HaveSME2 ())) : Bool)
    then
      (do
        (HaveSMEI16I64 ()))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLALL_ZA_ZZi_D2xi 128 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLALL_ZA_ZZi_D2xi 256 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLALL_ZA_ZZi_D2xi 512 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLALL_ZA_ZZi_D2xi 1024 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLALL_ZA_ZZi_D2xi 2048 esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
