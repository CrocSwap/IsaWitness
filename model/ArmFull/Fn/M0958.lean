import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M0873
import ArmFull.Fn.M0874

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

def decode_SQADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SQADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SQADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SQADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SQADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_UQSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UQSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UQSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UQSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UQSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UQSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_SQSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SQSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SQSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SQSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SQSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_UQADD_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UQADD_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_UQADD_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_UQADD_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_UQADD_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_UQADD_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_SQADD_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQADD_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_SQADD_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_SQADD_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_SQADD_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_SQADD_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_UQSUB_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UQSUB_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_UQSUB_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_UQSUB_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_UQSUB_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_UQSUB_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_SQSUB_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQSUB_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_SQSUB_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_SQSUB_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_SQSUB_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_SQSUB_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_BRKPA_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let m : Int := (BitVec.toNat Pm)
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BRKPA_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKPA_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKPA_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKPA_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKPA_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_BRKPAS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let m : Int := (BitVec.toNat Pm)
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BRKPAS_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKPAS_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKPAS_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKPAS_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKPAS_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_BRKPB_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let m : Int := (BitVec.toNat Pm)
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BRKPB_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKPB_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKPB_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKPB_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKPB_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_BRKPBS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let m : Int := (BitVec.toNat Pm)
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BRKPBS_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKPBS_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKPBS_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKPBS_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKPBS_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_BRKN_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let dm : Int := (BitVec.toNat Pdm)
  let setflags : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BRKN_P_P_PP__ 128 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKN_P_P_PP__ 256 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKN_P_P_PP__ 512 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKN_P_P_PP__ 1024 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKN_P_P_PP__ 2048 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_BRKNS_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Pn)
  let dm : Int := (BitVec.toNat Pdm)
  let setflags : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BRKNS_P_P_PP__ 128 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 256 =>
    (do
      (execute_BRKNS_P_P_PP__ 256 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 512 =>
    (do
      (execute_BRKNS_P_P_PP__ 512 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 1024 =>
    (do
      (execute_BRKNS_P_P_PP__ 1024 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | 2048 =>
    (do
      (execute_BRKNS_P_P_PP__ 2048 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) setflags))
  | _ => (pure (()))


def decode_INSR_Z_V__ (size : (BitVec 2)) (Vm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Vm)
  match VL with
  | 128 =>
    (do
      (execute_INSR_Z_V__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_INSR_Z_V__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_INSR_Z_V__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_INSR_Z_V__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_INSR_Z_V__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


end ArmFull.Functions
