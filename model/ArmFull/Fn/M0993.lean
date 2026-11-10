import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0906
import ArmFull.Fn.M0907
import ArmFull.Fn.M0908

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

def decode_UMLALL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLALL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLALL_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLALL_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLALL_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLALL_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLALL_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSLL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLSLL_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSLL_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSLL_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSLL_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSLL_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_USMLALL_ZA_ZZW_S2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_USMLALL_ZA_ZZW_S2x2 128 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_USMLALL_ZA_ZZW_S2x2 256 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_USMLALL_ZA_ZZW_S2x2 512 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_USMLALL_ZA_ZZW_S2x2 1024 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_USMLALL_ZA_ZZW_S2x2 2048 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLALL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZV_2x1 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZV_2x1 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZV_2x1 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZV_2x1 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZV_2x1 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZV_2x1 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZV_2x1 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZV_2x1 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZV_2x1 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZV_2x1 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLALL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLALL_ZA_ZZV_2x1 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLALL_ZA_ZZV_2x1 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLALL_ZA_ZZV_2x1 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLALL_ZA_ZZV_2x1 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLALL_ZA_ZZV_2x1 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SMLSLL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SMLSLL_ZA_ZZV_2x1 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SMLSLL_ZA_ZZV_2x1 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SMLSLL_ZA_ZZV_2x1 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SMLSLL_ZA_ZZV_2x1 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SMLSLL_ZA_ZZV_2x1 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_USMLALL_ZA_ZZV_S2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_USMLALL_ZA_ZZV_S2x1 128 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_USMLALL_ZA_ZZV_S2x1 256 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_USMLALL_ZA_ZZV_S2x1 512 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_USMLALL_ZA_ZZV_S2x1 1024 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_USMLALL_ZA_ZZV_S2x1 2048 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SUMLALL_ZA_ZZV_S2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SUMLALL_ZA_ZZV_S2x1 128 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUMLALL_ZA_ZZV_S2x1 256 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUMLALL_ZA_ZZV_S2x1 512 esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUMLALL_ZA_ZZV_S2x1 1024 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUMLALL_ZA_ZZV_S2x1 2048 esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLALL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_UMLALL_ZA_ZZW_4x4 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLALL_ZA_ZZW_4x4 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLALL_ZA_ZZW_4x4 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLALL_ZA_ZZW_4x4 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLALL_ZA_ZZW_4x4 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_UMLSLL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_UMLSLL_ZA_ZZW_4x4 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_UMLSLL_ZA_ZZW_4x4 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_UMLSLL_ZA_ZZW_4x4 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_UMLSLL_ZA_ZZW_4x4 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_UMLSLL_ZA_ZZW_4x4 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
