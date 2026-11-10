import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M1113
import ArmFull.Fn.M1114
import ArmFull.Fn.M1115

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

def decode_FCVT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FCVT_Z_P_Z_D2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let d_esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_D2H 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_D2H 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_D2H 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_D2H 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_D2H 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FCVT_Z_P_Z_S2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_S2D 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_S2D 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_S2D 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_S2D 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_S2D 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FCVT_Z_P_Z_H2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_H2D 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_H2D 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_H2D 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_H2D 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_H2D 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FCVT_Z_P_Z_H2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_H2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_H2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_H2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_H2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_H2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FCVT_Z_P_Z_S2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let d_esize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_P_Z_S2H 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVT_Z_P_Z_S2H 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVT_Z_P_Z_S2H 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVT_Z_P_Z_S2H 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVT_Z_P_Z_S2H 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


def decode_FSQRT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FSQRT_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FSQRT_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FSQRT_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FSQRT_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FSQRT_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FABD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FABD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FABD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FABD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FABD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FABD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FDIV_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FDIV_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FDIV_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FDIV_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FDIV_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FDIV_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FDIVR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FDIVR_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FDIVR_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FDIVR_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FDIVR_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FDIVR_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FMAXNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FMAXNM_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FMAXNM_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FMAXNM_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FMAXNM_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FMAXNM_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FMINNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FMINNM_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FMINNM_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FMINNM_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FMINNM_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FMINNM_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FMAX_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FMAX_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FMAX_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FMAX_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FMAX_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FMAX_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_FMIN_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_FMIN_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_FMIN_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_FMIN_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_FMIN_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_FMIN_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


end ArmFull.Functions
