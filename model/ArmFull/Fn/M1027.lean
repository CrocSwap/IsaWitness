import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0202
import ArmFull.Fn.M0984
import ArmFull.Fn.M0985
import ArmFull.Fn.M0990
import ArmFull.Fn.M0991
import ArmFull.Fn.M0992

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

def decode_PRFH_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_BZ_D_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_BZ_D_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_BZ_D_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_BZ_D_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_BZ_D_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_BZ_D_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_BZ_D_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_BZ_D_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_BZ_D_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_BZ_D_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_BZ_D_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_BZ_D_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_BZ_D_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_BZ_D_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_BZ_D_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFB_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 0
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_AI_D 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_AI_D 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_AI_D 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_AI_D 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_AI_D 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 1
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_AI_D 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_AI_D 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_AI_D 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_AI_D 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_AI_D 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 2
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_AI_D 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_AI_D 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_AI_D 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_AI_D 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_AI_D 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 3
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_AI_D 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_AI_D 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_AI_D 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_AI_D 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_AI_D 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFB_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 64
  let offs_unsigned : Bool := true
  let scale : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_BZ_D_64_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_BZ_D_64_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_BZ_D_64_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_BZ_D_64_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_BZ_D_64_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 64
  let offs_unsigned : Bool := true
  let scale : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_BZ_D_64_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_BZ_D_64_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_BZ_D_64_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_BZ_D_64_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_BZ_D_64_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 64
  let offs_unsigned : Bool := true
  let scale : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_BZ_D_64_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_BZ_D_64_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_BZ_D_64_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_BZ_D_64_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_BZ_D_64_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 64
  let offs_unsigned : Bool := true
  let scale : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_BZ_D_64_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_BZ_D_64_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_BZ_D_64_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_BZ_D_64_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_BZ_D_64_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SME__seg9 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__659 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 5 3)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
    then
      (do
        let w__658 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__658 <b 2523) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__659 : Bool)
  then
    (do
      writeReg SEE 2523
      let Zm := (BitVec.slice __opcode 16 4)
      let Rv := (BitVec.slice __opcode 13 2)
      let i2 := (BitVec.slice __opcode 10 2)
      let Zn := (BitVec.slice __opcode 6 4)
      let U := (BitVec.slice __opcode 4 1)
      let off3 := (BitVec.slice __opcode 0 3)
      (decode_UDOT_ZA_ZZi_S2xi Zm Rv i2 Zn U off3)
      (pure false))
  else
    (do
      let w__661 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 5 3)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
        then
          (do
            let w__660 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__660 <b 2524) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__661 : Bool)
      then
        (do
          writeReg SEE 2524
          let Zm := (BitVec.slice __opcode 16 4)
          let Rv := (BitVec.slice __opcode 13 2)
          let i2 := (BitVec.slice __opcode 10 2)
          let Zn := (BitVec.slice __opcode 6 4)
          let U := (BitVec.slice __opcode 4 1)
          let off3 := (BitVec.slice __opcode 0 3)
          (decode_SDOT_ZA_ZZi_S2xi Zm Rv i2 Zn U off3)
          (pure false))
      else
        (do
          let w__663 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 5 3)) == (0b101#3 : (BitVec 3)))))) : Bool) : Bool)
            then
              (do
                let w__662 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__662 <b 2525) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__663 : Bool)
          then
            (do
              writeReg SEE 2525
              let Zm := (BitVec.slice __opcode 16 4)
              let Rv := (BitVec.slice __opcode 13 2)
              let i2 := (BitVec.slice __opcode 10 2)
              let Zn := (BitVec.slice __opcode 6 4)
              let U := (BitVec.slice __opcode 4 1)
              let off3 := (BitVec.slice __opcode 0 3)
              (decode_USDOT_ZA_ZZi_S2xi Zm Rv i2 Zn U off3)
              (pure false))
          else
            (do
              let w__665 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 5 3)) == (0b111#3 : (BitVec 3)))))) : Bool) : Bool)
                then
                  (do
                    let w__664 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__664 <b 2526) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__665 : Bool)
              then
                (do
                  writeReg SEE 2526
                  let Zm := (BitVec.slice __opcode 16 4)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let i2 := (BitVec.slice __opcode 10 2)
                  let Zn := (BitVec.slice __opcode 6 4)
                  let U := (BitVec.slice __opcode 4 1)
                  let off3 := (BitVec.slice __opcode 0 3)
                  (decode_SUDOT_ZA_ZZi_S2xi Zm Rv i2 Zn U off3)
                  (pure false))
              else
                (do
                  let w__667 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                    then
                      (do
                        let w__666 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__666 <b 2527) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__667 : Bool)
                  then
                    (do
                      writeReg SEE 2527
                      let Zm := (BitVec.slice __opcode 16 4)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let i1 := (BitVec.slice __opcode 10 1)
                      let Zn := (BitVec.slice __opcode 6 4)
                      let U := (BitVec.slice __opcode 4 1)
                      let off3 := (BitVec.slice __opcode 0 3)
                      (decode_UDOT_ZA_ZZi_D2xi Zm Rv i1 Zn U off3)
                      (pure false))
                  else
                    (do
                      let w__669 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                        then
                          (do
                            let w__668 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__668 <b 2528) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__669 : Bool)
                      then
                        (do
                          writeReg SEE 2528
                          let Zm := (BitVec.slice __opcode 16 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let i1 := (BitVec.slice __opcode 10 1)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let U := (BitVec.slice __opcode 4 1)
                          let off3 := (BitVec.slice __opcode 0 3)
                          (decode_SDOT_ZA_ZZi_D2xi Zm Rv i1 Zn U off3)
                          (pure false))
                      else
                        (do
                          let w__671 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 6 3)) == (0x6#4 : (BitVec 4)))))) : Bool) : Bool)
                            then
                              (do
                                let w__670 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__670 <b 2529) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__671 : Bool)
                          then
                            (do
                              writeReg SEE 2529
                              let Zm := (BitVec.slice __opcode 16 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let i2 := (BitVec.slice __opcode 10 2)
                              let Zn := (BitVec.slice __opcode 7 3)
                              let U := (BitVec.slice __opcode 4 1)
                              let off3 := (BitVec.slice __opcode 0 3)
                              (decode_UDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U off3)
                              (pure false))
                          else
                            (do
                              let w__673 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 6 3)) == (0x4#4 : (BitVec 4)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__672 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__672 <b 2530) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__673 : Bool)
                              then
                                (do
                                  writeReg SEE 2530
                                  let Zm := (BitVec.slice __opcode 16 4)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let i2 := (BitVec.slice __opcode 10 2)
                                  let Zn := (BitVec.slice __opcode 7 3)
                                  let U := (BitVec.slice __opcode 4 1)
                                  let off3 := (BitVec.slice __opcode 0 3)
                                  (decode_SDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U off3)
                                  (pure false))
                              else
                                (do
                                  let w__675 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 6 3)) == (0x5#4 : (BitVec 4)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__674 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__674 <b 2531) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__675 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2531
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let i2 := (BitVec.slice __opcode 10 2)
                                      let Zn := (BitVec.slice __opcode 7 3)
                                      let U := (BitVec.slice __opcode 4 1)
                                      let off3 := (BitVec.slice __opcode 0 3)
                                      (decode_USDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U off3)
                                      (pure false))
                                  else
                                    (do
                                      let w__677 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 6 3)) == (0x7#4 : (BitVec 4)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__676 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__676 <b 2532) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__677 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2532
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let i2 := (BitVec.slice __opcode 10 2)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let U := (BitVec.slice __opcode 4 1)
                                          let off3 := (BitVec.slice __opcode 0 3)
                                          (decode_SUDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U off3)
                                          (pure false))
                                      else
                                        (do
                                          let w__679 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__678 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__678 <b 2533) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__679 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2533
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let i1 := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 7 3)
                                              let U := (BitVec.slice __opcode 4 1)
                                              let off3 := (BitVec.slice __opcode 0 3)
                                              (decode_UDOT_ZA_ZZi_D4xi Zm Rv i1 Zn U off3)
                                              (pure false))
                                          else
                                            (do
                                              let w__681 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 6 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__680 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__680 <b 2534) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__681 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2534
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let i1 := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 7 3)
                                                  let U := (BitVec.slice __opcode 4 1)
                                                  let off3 := (BitVec.slice __opcode 0 3)
                                                  (decode_SDOT_ZA_ZZi_D4xi Zm Rv i1 Zn U off3)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__683 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 6 3)) == (0x6#4 : (BitVec 4)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__682 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__682 <b 2535) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__683 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2535
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let i2 := (BitVec.slice __opcode 10 2)
                                                      let Zn := (BitVec.slice __opcode 7 3)
                                                      let U := (BitVec.slice __opcode 4 1)
                                                      let off3 := (BitVec.slice __opcode 0 3)
                                                      (decode_UVDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U off3)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__685 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 6 3)) == (0x4#4 : (BitVec 4)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__684 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__684 <b 2536) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__685 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2536
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let i2 := (BitVec.slice __opcode 10 2)
                                                          let Zn := (BitVec.slice __opcode 7 3)
                                                          let U := (BitVec.slice __opcode 4 1)
                                                          let off3 := (BitVec.slice __opcode 0 3)
                                                          (decode_SVDOT_ZA_ZZi_S4xi Zm Rv i2 Zn U
                                                            off3)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__687 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 6 3)) == (0x5#4 : (BitVec 4)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__686 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__686 <b 2537) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__687 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2537
                                                              let Zm := (BitVec.slice __opcode 16 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let i2 := (BitVec.slice __opcode 10 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let U := (BitVec.slice __opcode 4 1)
                                                              let off3 :=
                                                                (BitVec.slice __opcode 0 3)
                                                              (decode_USVDOT_ZA_ZZi_S4xi Zm Rv i2 Zn
                                                                U off3)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__689 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 6 3)) == (0x7#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__688 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__688 <b 2538) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__689 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2538
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let i2 :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 7 3)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_SUVDOT_ZA_ZZi_S4xi Zm Rv
                                                                    i2 Zn U off3)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__691 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 12 11)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__690 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__690 <b 2539) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__691 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2539
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let i1 :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 7 3)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 0 3)
                                                                      (decode_UVDOT_ZA_ZZi_D4xi Zm
                                                                        Rv i1 Zn U off3)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__693 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 12 11)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 6 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__692 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__692 <b 2540) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__693 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2540
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let i1 :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 7
                                                                              3)
                                                                          let U :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let off3 :=
                                                                            (BitVec.slice __opcode 0
                                                                              3)
                                                                          (decode_SVDOT_ZA_ZZi_D4xi
                                                                            Zm Rv i1 Zn U off3)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__695 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 16
                                                                                       15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 12
                                                                                         10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 5
                                                                                         3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__694 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__694 <b 2541) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__695 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2541
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 4)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 4)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let off3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 3)
                                                                              (decode_UDOT_ZA32_ZZW_2x2
                                                                                Zm Rv Zn U off3)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__697 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             12 10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__696 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__696 <b 2542) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__697 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2542
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 17 4)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let off3 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_SDOT_ZA32_ZZW_2x2
                                                                                    Zm Rv Zn U off3)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__699 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 12
                                                                                                 10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__698 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__698 <b 2543) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__699 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2543
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let off3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          3)
                                                                                      (decode_UDOT_ZA32_ZZV_2x1
                                                                                        Zm Rv Zn U
                                                                                        off3)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__701 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     12
                                                                                                     10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__700 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__700 <b 2544) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__701 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2544
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let off3 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 3)
                                                                                          (decode_SDOT_ZA32_ZZV_2x1
                                                                                            Zm Rv Zn
                                                                                            U off3)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__703 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       17
                                                                                                       15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         12
                                                                                                         10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         6
                                                                                                         3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__702 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__702 <b 2545) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__703 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2545
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  18
                                                                                                  3)
                                                                                              let Rv :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  7
                                                                                                  3)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let off3 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_UDOT_ZA32_ZZW_4x4
                                                                                                Zm
                                                                                                Rv
                                                                                                Zn U
                                                                                                off3)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__705 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           17
                                                                                                           15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             12
                                                                                                             10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             6
                                                                                                             3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__704 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__704 <b 2546) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__705 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2546
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      18
                                                                                                      3)
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      3)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let off3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      3)
                                                                                                  (decode_SDOT_ZA32_ZZW_4x4
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    Zn
                                                                                                    U
                                                                                                    off3)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__707 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__706 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__706 <b 2547) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__707 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2547
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let off3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_UDOT_ZA32_ZZV_4x1
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        Zn
                                                                                                        U
                                                                                                        off3)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__709 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__708 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__708 <b 2548) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__709 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2548
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let off3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_SDOT_ZA32_ZZV_4x1
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            Zn
                                                                                                            U
                                                                                                            off3)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__711 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         5
                                                                                                                         3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__710 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__710 <b 2549) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__711 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2549
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rv :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let i2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  2)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  4)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  1)
                                                                                                              let off3 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_UDOT_ZA32_ZZi_2xi
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                i2
                                                                                                                Zn
                                                                                                                U
                                                                                                                off3)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__713 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             12
                                                                                                                             12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             5
                                                                                                                             3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__712 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__712 <b 2550) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__713 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2550
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Rv :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let i2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      2)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      6
                                                                                                                      4)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      1)
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_SDOT_ZA32_ZZi_2xi
                                                                                                                    Zm
                                                                                                                    Rv
                                                                                                                    i2
                                                                                                                    Zn
                                                                                                                    U
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__715 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 12
                                                                                                                                 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 6
                                                                                                                                 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__714 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__714 <b 2551) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__715 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2551
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rv :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          2)
                                                                                                                      let i2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          2)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          7
                                                                                                                          3)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let off3 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_UDOT_ZA32_ZZi_4xi
                                                                                                                        Zm
                                                                                                                        Rv
                                                                                                                        i2
                                                                                                                        Zn
                                                                                                                        U
                                                                                                                        off3)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__717 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     12
                                                                                                                                     12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     6
                                                                                                                                     3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__716 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__716 <b 2552) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__717 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2552
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Rv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let i2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              3)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let off3 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              3)
                                                                                                                          (decode_SDOT_ZA32_ZZi_4xi
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            i2
                                                                                                                            Zn
                                                                                                                            U
                                                                                                                            off3)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__719 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         12
                                                                                                                                         12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         5
                                                                                                                                         3)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__718 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__718 <b 2553) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__719 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2553
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Rv :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let i2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  4)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  1)
                                                                                                                              let off3 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_UVDOT_ZA32_ZZi_2xi
                                                                                                                                Zm
                                                                                                                                Rv
                                                                                                                                i2
                                                                                                                                Zn
                                                                                                                                U
                                                                                                                                off3)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__721 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             12
                                                                                                                                             12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             3)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__720 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__720 <b 2554) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__721 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2554
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Rv :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      2)
                                                                                                                                  let i2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      4)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      1)
                                                                                                                                  let off3 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      3)
                                                                                                                                  (decode_SVDOT_ZA32_ZZi_2xi
                                                                                                                                    Zm
                                                                                                                                    Rv
                                                                                                                                    i2
                                                                                                                                    Zn
                                                                                                                                    U
                                                                                                                                    off3)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__723 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   12
                                                                                                                                                   10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   2)) == (0b100#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__722 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__722 <b 2555) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__723 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2555
                                                                                                                                      let sz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Rv :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          2)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          3
                                                                                                                                          1)
                                                                                                                                      let off2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          2)
                                                                                                                                      (decode_UMLALL_ZA_ZZV_1
                                                                                                                                        sz
                                                                                                                                        Zm
                                                                                                                                        Rv
                                                                                                                                        Zn
                                                                                                                                        U
                                                                                                                                        S
                                                                                                                                        off2)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__725 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       12
                                                                                                                                                       10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       4
                                                                                                                                                       2)) == (0b110#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__724 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__724 <b 2556) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__725 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2556
                                                                                                                                          let sz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rv :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              2)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              4
                                                                                                                                              1)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              3
                                                                                                                                              1)
                                                                                                                                          let off2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              2)
                                                                                                                                          (decode_UMLSLL_ZA_ZZV_1
                                                                                                                                            sz
                                                                                                                                            Zm
                                                                                                                                            Rv
                                                                                                                                            Zn
                                                                                                                                            U
                                                                                                                                            S
                                                                                                                                            off2)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
