import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0884
import ArmFull.Fn.M0885

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

def decode_SMLALB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_SMLALB_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLALB_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLALB_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLALB_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLALB_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLALT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLALT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLALT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLALT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLALT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLALT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLALT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLALT_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLALT_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLALT_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLALT_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLALT_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLALB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_UMLALB_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLALB_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLALB_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLALB_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLALB_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLALB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_UMLALB_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLALB_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLALB_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLALB_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLALB_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLALT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLALT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLALT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLALT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLALT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLALT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLALT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLALT_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLALT_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLALT_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLALT_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLALT_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLSLB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_SMLSLB_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLSLB_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLSLB_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLSLB_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLSLB_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLSLB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_SMLSLB_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLSLB_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLSLB_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLSLB_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLSLB_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLSLT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLSLT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLSLT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLSLT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLSLT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLSLT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_SMLSLT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_SMLSLT_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_SMLSLT_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_SMLSLT_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_SMLSLT_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_SMLSLT_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLSLB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_UMLSLB_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLSLB_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLSLB_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLSLB_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLSLB_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLSLB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i2h +++ i2l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_UMLSLB_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLSLB_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLSLB_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLSLB_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLSLB_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


def decode_UMLSLT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_UMLSLT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 256 =>
    (do
      (execute_UMLSLT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 512 =>
    (do
      (execute_UMLSLT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 1024 =>
    (do
      (execute_UMLSLT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | 2048 =>
    (do
      (execute_UMLSLT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel))
  | _ => (pure (()))


end ArmFull.Functions
