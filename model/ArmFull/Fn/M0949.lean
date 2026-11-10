import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0866

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

def decode_UADDV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  match VL with
  | 128 =>
    (do
      (execute_UADDV_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UADDV_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UADDV_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UADDV_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UADDV_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UMAXV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAXV_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UMAXV_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UMAXV_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UMAXV_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UMAXV_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_SMAXV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAXV_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SMAXV_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SMAXV_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SMAXV_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SMAXV_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_UMINV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMINV_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UMINV_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UMINV_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UMINV_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UMINV_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_SMINV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMINV_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SMINV_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SMINV_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SMINV_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SMINV_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


def decode_INDEX_Z_II__ (size : (BitVec 2)) (imm5b : (BitVec 5)) (imm5 : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let d : Int := (BitVec.toNat Zd)
  let imm1 : Int := (BitVec.toInt imm5)
  let imm2 : Int := (BitVec.toInt imm5b)
  match VL with
  | 128 =>
    (do
      (execute_INDEX_Z_II__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm1
        imm2))
  | 256 =>
    (do
      (execute_INDEX_Z_II__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm1
        imm2))
  | 512 =>
    (do
      (execute_INDEX_Z_II__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm1
        imm2))
  | 1024 =>
    (do
      (execute_INDEX_Z_II__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm1
        imm2))
  | 2048 =>
    (do
      (execute_INDEX_Z_II__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm1
        imm2))
  | _ => (pure (()))


def decode_INDEX_Z_IR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (imm5 : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Zd)
  let imm : Int := (BitVec.toInt imm5)
  match VL with
  | 128 =>
    (do
      (execute_INDEX_Z_IR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_INDEX_Z_IR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_INDEX_Z_IR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_INDEX_Z_IR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_INDEX_Z_IR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_INDEX_Z_RI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Zd)
  let imm : Int := (BitVec.toInt imm5)
  match VL with
  | 128 =>
    (do
      (execute_INDEX_Z_RI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_INDEX_Z_RI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_INDEX_Z_RI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_INDEX_Z_RI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_INDEX_Z_RI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) imm
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_INDEX_Z_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_INDEX_Z_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_INDEX_Z_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_INDEX_Z_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_INDEX_Z_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_INDEX_Z_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_AND_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector_at (← occLabel 5375) 64) ) : SailM (BitVec 64) )
  let (__tup_0, _) ← (( do
    (DecodeBitMasks (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm13 12)]))
      (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64) ) : SailM
    ((BitVec 64) × (BitVec 64)) )
  let imm : (BitVec 64) := __tup_0
  match VL with
  | 128 =>
    (do
      (execute_AND_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) imm))
  | 256 =>
    (do
      (execute_AND_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) imm))
  | 512 =>
    (do
      (execute_AND_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) imm))
  | 1024 =>
    (do
      (execute_AND_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) imm))
  | 2048 =>
    (do
      (execute_AND_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) imm))
  | _ => (pure (()))


def decode_EOR_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector_at (← occLabel 5377) 64) ) : SailM (BitVec 64) )
  let (__tup_0, _) ← (( do
    (DecodeBitMasks (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm13 12)]))
      (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64) ) : SailM
    ((BitVec 64) × (BitVec 64)) )
  let imm : (BitVec 64) := __tup_0
  match VL with
  | 128 =>
    (do
      (execute_EOR_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) imm))
  | 256 =>
    (do
      (execute_EOR_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) imm))
  | 512 =>
    (do
      (execute_EOR_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) imm))
  | 1024 =>
    (do
      (execute_EOR_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) imm))
  | 2048 =>
    (do
      (execute_EOR_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) imm))
  | _ => (pure (()))


def decode_ORR_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector_at (← occLabel 5379) 64) ) : SailM (BitVec 64) )
  let (__tup_0, _) ← (( do
    (DecodeBitMasks (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm13 12)]))
      (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64) ) : SailM
    ((BitVec 64) × (BitVec 64)) )
  let imm : (BitVec 64) := __tup_0
  match VL with
  | 128 =>
    (do
      (execute_ORR_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) imm))
  | 256 =>
    (do
      (execute_ORR_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) imm))
  | 512 =>
    (do
      (execute_ORR_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) imm))
  | 1024 =>
    (do
      (execute_ORR_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) imm))
  | 2048 =>
    (do
      (execute_ORR_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) imm))
  | _ => (pure (()))


def decode_MAD_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Za : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let a : Int := (BitVec.toNat Za)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_MAD_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 256 =>
    (do
      (execute_MAD_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 512 =>
    (do
      (execute_MAD_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 1024 =>
    (do
      (execute_MAD_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 2048 =>
    (do
      (execute_MAD_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | _ => (pure (()))


def decode_MSB_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Za : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let a : Int := (BitVec.toNat Za)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_MSB_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 256 =>
    (do
      (execute_MSB_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 512 =>
    (do
      (execute_MSB_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 1024 =>
    (do
      (execute_MSB_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | 2048 =>
    (do
      (execute_MSB_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))
        sub_op))
  | _ => (pure (()))


def decode_MLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_MLA_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_MLA_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_MLA_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_MLA_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_MLA_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


end ArmFull.Functions
