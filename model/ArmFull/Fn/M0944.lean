import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M0862
import ArmFull.Fn.M0863

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

def decode_SQINCP_R_P_R_SX (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_SQINCP_R_P_R_SX 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_SQINCP_R_P_R_SX 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_SQINCP_R_P_R_SX 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_SQINCP_R_P_R_SX 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_SQINCP_R_P_R_SX 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_UQINCP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_UQINCP_R_P_R_X 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_UQINCP_R_P_R_X 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_UQINCP_R_P_R_X 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_UQINCP_R_P_R_X 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_UQINCP_R_P_R_X 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_SQINCP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_SQINCP_R_P_R_X 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_SQINCP_R_P_R_X 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_SQINCP_R_P_R_X 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_SQINCP_R_P_R_X 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_SQINCP_R_P_R_X 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_UQDECP_R_P_R_UW (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_UQDECP_R_P_R_UW 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_UQDECP_R_P_R_UW 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_UQDECP_R_P_R_UW 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_UQDECP_R_P_R_UW 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_UQDECP_R_P_R_UW 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_SQDECP_R_P_R_SX (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_SQDECP_R_P_R_SX 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_SQDECP_R_P_R_SX 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_SQDECP_R_P_R_SX 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_SQDECP_R_P_R_SX 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_SQDECP_R_P_R_SX 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_UQDECP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_UQDECP_R_P_R_X 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_UQDECP_R_P_R_X 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_UQDECP_R_P_R_X 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_UQDECP_R_P_R_X 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_UQDECP_R_P_R_X 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_SQDECP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize : Nat := 64
  match VL with
  | 128 =>
    (do
      (execute_SQDECP_R_P_R_X 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 256 =>
    (do
      (execute_SQDECP_R_P_R_X 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 512 =>
    (do
      (execute_SQDECP_R_P_R_X 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 1024 =>
    (do
      (execute_SQDECP_R_P_R_X 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | 2048 =>
    (do
      (execute_SQDECP_R_P_R_X 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) ssize is_unsigned))
  | _ => (pure (()))


def decode_DECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_DECP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_DECP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_DECP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_DECP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_DECP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_INCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_INCP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_INCP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_INCP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_INCP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_INCP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_UQINCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UQINCP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 256 =>
    (do
      (execute_UQINCP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 512 =>
    (do
      (execute_UQINCP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 1024 =>
    (do
      (execute_UQINCP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 2048 =>
    (do
      (execute_UQINCP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | _ => (pure (()))


def decode_SQINCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQINCP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 256 =>
    (do
      (execute_SQINCP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 512 =>
    (do
      (execute_SQINCP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 1024 =>
    (do
      (execute_SQINCP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 2048 =>
    (do
      (execute_SQINCP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | _ => (pure (()))


def decode_UQDECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UQDECP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 256 =>
    (do
      (execute_UQDECP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 512 =>
    (do
      (execute_UQDECP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 1024 =>
    (do
      (execute_UQDECP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 2048 =>
    (do
      (execute_UQDECP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | _ => (pure (()))


def decode_SQDECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Pm)
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SQDECP_Z_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 256 =>
    (do
      (execute_SQDECP_Z_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 512 =>
    (do
      (execute_SQDECP_Z_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 1024 =>
    (do
      (execute_SQDECP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | 2048 =>
    (do
      (execute_SQDECP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) is_unsigned))
  | _ => (pure (()))


def decode_DECB_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_DECB_R_RS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_DECB_R_RS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_DECB_R_RS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_DECB_R_RS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_DECB_R_RS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


def decode_DECH_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm : Int := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 =>
    (do
      (execute_DECH_R_RS__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 256 =>
    (do
      (execute_DECH_R_RS__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 512 =>
    (do
      (execute_DECH_R_RS__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 1024 =>
    (do
      (execute_DECH_R_RS__ 1024 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | 2048 =>
    (do
      (execute_DECH_R_RS__ 2048 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (imm)) pat))
  | _ => (pure (()))


end ArmFull.Functions
