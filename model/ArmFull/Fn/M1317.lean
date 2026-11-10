import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M1194
import ArmFull.Fn.M1195
import ArmFull.Fn.M1196

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

def decode_LD1RB_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 8
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RB_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RB_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RB_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RB_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RB_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSW_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 32
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSW_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSW_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSW_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSW_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSW_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RH_Z_P_BI_U16 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let msize : Nat := 16
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RH_Z_P_BI_U16 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RH_Z_P_BI_U16 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RH_Z_P_BI_U16 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RH_Z_P_BI_U16 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RH_Z_P_BI_U16 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RH_Z_P_BI_U32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 16
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RH_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RH_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RH_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RH_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RH_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RH_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 16
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RH_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RH_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RH_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RH_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RH_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSH_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 16
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSH_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSH_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSH_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSH_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSH_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSH_Z_P_BI_S32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 16
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSH_Z_P_BI_S32 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSH_Z_P_BI_S32 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSH_Z_P_BI_S32 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSH_Z_P_BI_S32 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSH_Z_P_BI_S32 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RW_Z_P_BI_U32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 32
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RW_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RW_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RW_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RW_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RW_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RW_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 32
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RW_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RW_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RW_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RW_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RW_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSB_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 8
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSB_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSB_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSB_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSB_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSB_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSB_Z_P_BI_S32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 32
  let msize : Nat := 8
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSB_Z_P_BI_S32 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSB_Z_P_BI_S32 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSB_Z_P_BI_S32 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSB_Z_P_BI_S32 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSB_Z_P_BI_S32 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RSB_Z_P_BI_S16 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 16
  let msize : Nat := 8
  let is_unsigned : Bool := false
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RSB_Z_P_BI_S16 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RSB_Z_P_BI_S16 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RSB_Z_P_BI_S16 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RSB_Z_P_BI_S16 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RSB_Z_P_BI_S16 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


def decode_LD1RD_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let t : Int := (BitVec.toNat Zt)
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat Pg)
  let esize : Nat := 64
  let msize : Nat := 64
  let is_unsigned : Bool := true
  let offset : Int := (BitVec.toNat imm6)
  match VL with
  | 128 =>
    (do
      (execute_LD1RD_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 256 =>
    (do
      (execute_LD1RD_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 512 =>
    (do
      (execute_LD1RD_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 1024 =>
    (do
      (execute_LD1RD_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | 2048 =>
    (do
      (execute_LD1RD_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))
        is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
