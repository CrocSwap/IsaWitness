import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M1081
import ArmFull.Fn.M1082

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

def decode_FCVTZU_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_D2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_S2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_S2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_D2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_S2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_S2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_FP162H (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 16
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162H 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162H 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162H 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162H 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162H 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_FP162W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_Z_P_Z_FP162X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_Z_P_Z_FP162X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_FP162H (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 16
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162H 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162H 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162H 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162H 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162H 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_FP162W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162W 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162W 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162W 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_Z_P_Z_FP162X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162X 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162X 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162X 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_Z_P_Z_FP162X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
