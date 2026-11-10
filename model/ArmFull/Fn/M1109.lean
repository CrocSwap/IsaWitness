import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0017
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M1078
import ArmFull.Fn.M1079

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

def decode_ldsmax_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4380) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4381) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4382) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsmin_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4383) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsminb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4384) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsminh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4385) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldumax_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4386) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldumaxb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4387) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldumaxh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4388) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldumin_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4389) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_lduminb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4390) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_lduminh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4391) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveLSE128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4438) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b001 => MemAtomicOp_BIC
    | 0b011 => MemAtomicOp_ORR
    | _ => op
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld_128_ldclrp acquire (Sail.Int.toNatChecked (n)) op
    release (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveLSE128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4582) ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match opc with
    | 0b001 => MemAtomicOp_BIC
    | 0b011 => MemAtomicOp_ORR
    | _ => op
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld_128_ldsetp acquire (Sail.Int.toNatChecked (n)) op
    release (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwcas_aarch64_instrs_memory_rcw_cas (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_cas acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwcasp_aarch64_instrs_memory_rcw_cas_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rs 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_cas_128 acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwclr_aarch64_instrs_memory_rcw_ld_rcwclr (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_rcwclr acquire (Sail.Int.toNatChecked (n)) op release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwclrp_aarch64_instrs_memory_rcw_ld_128_rcwclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rt2 == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let n : Int := (BitVec.toNat Rn)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_128_rcwclrp acquire (Sail.Int.toNatChecked (n)) op release
    soft (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked)


def decode_rcwscas_aarch64_instrs_memory_rcws_cas (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_cas acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwscasp_aarch64_instrs_memory_rcws_cas_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveTHExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rs 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_cas_128 acquire (Sail.Int.toNatChecked (n)) release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


def decode_rcwsclr_aarch64_instrs_memory_rcws_ld_rcwsclr (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveTHExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let s : Int := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_rcwsclr acquire (Sail.Int.toNatChecked (n)) op release
    (Sail.Int.toNatChecked (s)) soft (Sail.Int.toNatChecked (t)) tagchecked)


end ArmFull.Functions
