import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1120

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

def decode_FMLSLB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMLSLB_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_FMLSLB_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_FMLSLB_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_FMLSLB_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_FMLSLB_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


def decode_FMLSLT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMLSLT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_FMLSLT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_FMLSLT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_FMLSLT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_FMLSLT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


def decode_FMLALB_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMLALB_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 256 =>
    (do
      (execute_FMLALB_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 512 =>
    (do
      (execute_FMLALB_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 1024 =>
    (do
      (execute_FMLALB_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 2048 =>
    (do
      (execute_FMLALB_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | _ => (pure (()))


def decode_FMLALT_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMLALT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 256 =>
    (do
      (execute_FMLALT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 512 =>
    (do
      (execute_FMLALT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 1024 =>
    (do
      (execute_FMLALT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 2048 =>
    (do
      (execute_FMLALT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | _ => (pure (()))


def decode_FMLSLB_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMLSLB_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 256 =>
    (do
      (execute_FMLSLB_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 512 =>
    (do
      (execute_FMLSLB_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 1024 =>
    (do
      (execute_FMLSLB_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 2048 =>
    (do
      (execute_FMLSLB_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | _ => (pure (()))


def decode_FMLSLT_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMLSLT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 256 =>
    (do
      (execute_FMLSLT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 512 =>
    (do
      (execute_FMLSLT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 1024 =>
    (do
      (execute_FMLSLT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | 2048 =>
    (do
      (execute_FMLSLT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        op1_neg))
  | _ => (pure (()))


def decode_BFMLALB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_BFMLALB_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMLALB_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMLALB_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMLALB_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMLALB_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMLALT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_BFMLALT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMLALT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMLALT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMLALT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMLALT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMLSLB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMLSLB_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_BFMLSLB_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_BFMLSLB_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_BFMLSLB_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_BFMLSLB_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


def decode_BFMLSLT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMLSLT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_BFMLSLT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_BFMLSLT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_BFMLSLT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_BFMLSLT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


def decode_BFMLALB_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 =>
    (do
      (execute_BFMLALB_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMLALB_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMLALB_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMLALB_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMLALB_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMLALT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 =>
    (do
      (execute_BFMLALT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMLALT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMLALT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMLALT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMLALT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMLSLB_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMLSLB_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_BFMLSLB_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_BFMLSLB_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_BFMLSLB_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_BFMLSLB_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


def decode_BFMLSLT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMLSLT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 256 =>
    (do
      (execute_BFMLSLT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 512 =>
    (do
      (execute_BFMLSLT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 1024 =>
    (do
      (execute_BFMLSLT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | 2048 =>
    (do
      (execute_BFMLSLT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg))
  | _ => (pure (()))


end ArmFull.Functions
