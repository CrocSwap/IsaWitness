import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0892
import ArmFull.Fn.M0893

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

def decode_SMAXQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAXQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SMAXQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SMAXQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SMAXQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SMAXQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_UMAXQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAXQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UMAXQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UMAXQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UMAXQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UMAXQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_SMINQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMINQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SMINQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SMINQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SMINQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SMINQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_UMINQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMINQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UMINQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UMINQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UMINQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UMINQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_PMOV_Z_PI_B (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Zd)
  let esize : Nat := 8
  let imm : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PMOV_Z_PI_B 128 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_Z_PI_B 256 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_Z_PI_B 512 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_Z_PI_B 1024 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_Z_PI_B 2048 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_Z_PI_H (i1 : (BitVec 1)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Zd)
  let esize : Nat := 16
  let imm : Int := (BitVec.toNat i1)
  match VL with
  | 128 =>
    (do
      (execute_PMOV_Z_PI_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_Z_PI_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_Z_PI_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_Z_PI_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_Z_PI_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_Z_PI_S (i2 : (BitVec 2)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Zd)
  let esize : Nat := 32
  let imm : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_PMOV_Z_PI_S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_Z_PI_S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_Z_PI_S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_Z_PI_S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_Z_PI_S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_Z_PI_D (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Zd)
  let esize : Nat := 64
  let imm : Int := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 =>
    (do
      (execute_PMOV_Z_PI_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_Z_PI_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_Z_PI_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_Z_PI_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_Z_PI_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_P_ZI_B (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let esize : Nat := 8
  let imm : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PMOV_P_ZI_B 128 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_P_ZI_B 256 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_P_ZI_B 512 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_P_ZI_B 1024 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_P_ZI_B 2048 (Sail.Int.toNatChecked (d)) esize imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_P_ZI_H (i1 : (BitVec 1)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let esize : Nat := 16
  let imm : Int := (BitVec.toNat i1)
  match VL with
  | 128 =>
    (do
      (execute_PMOV_P_ZI_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_P_ZI_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_P_ZI_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_P_ZI_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_P_ZI_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_P_ZI_S (i2 : (BitVec 2)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let esize : Nat := 32
  let imm : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_PMOV_P_ZI_S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_P_ZI_S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_P_ZI_S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_P_ZI_S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_P_ZI_S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PMOV_P_ZI_D (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Pd)
  let esize : Nat := 64
  let imm : Int := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 =>
    (do
      (execute_PMOV_P_ZI_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PMOV_P_ZI_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PMOV_P_ZI_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PMOV_P_ZI_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PMOV_P_ZI_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (imm))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PEXT_PN_RR__ (size : (BitVec 2)) (imm2 : (BitVec 2)) (PNn : (BitVec 3)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (1#1 +++ PNn))
  let d : Int := (BitVec.toNat Pd)
  let part : Int := (BitVec.toNat imm2)
  match VL with
  | 128 =>
    (do
      (execute_PEXT_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 256 =>
    (do
      (execute_PEXT_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 512 =>
    (do
      (execute_PEXT_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 1024 =>
    (do
      (execute_PEXT_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 2048 =>
    (do
      (execute_PEXT_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | _ => (pure (()))


def decode_PEXT_PP_RR__ (size : (BitVec 2)) (i1 : (BitVec 1)) (PNn : (BitVec 3)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (1#1 +++ PNn))
  let d0 : Int := (BitVec.toNat Pd)
  let d1 : Nat := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat Pd) +i 1))) 16)
  let part : Int := (BitVec.toNat i1)
  match VL with
  | 128 =>
    (do
      (execute_PEXT_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) d1 (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 256 =>
    (do
      (execute_PEXT_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) d1 (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 512 =>
    (do
      (execute_PEXT_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) d1 (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 1024 =>
    (do
      (execute_PEXT_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) d1 (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | 2048 =>
    (do
      (execute_PEXT_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) d1 (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))
  | _ => (pure (()))


def decode_PTRUE_PN_I__ (size : (BitVec 2)) (PNd : (BitVec 3)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  match VL with
  | 128 =>
    (do
      (execute_PTRUE_PN_I__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))))
  | 256 =>
    (do
      (execute_PTRUE_PN_I__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))))
  | 512 =>
    (do
      (execute_PTRUE_PN_I__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))))
  | 1024 =>
    (do
      (execute_PTRUE_PN_I__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))))
  | 2048 =>
    (do
      (execute_PTRUE_PN_I__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))))
  | _ => (pure (()))


end ArmFull.Functions
