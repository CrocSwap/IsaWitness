module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1129 set_option backward.proofsInPublic true @[expose] public section

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

def decode_ldaddh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4370) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldclr_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4371) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldclrb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4372) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldclrh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4373) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldeor_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4374) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldeorb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4375) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldeorh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4376) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldset_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4377) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsetb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4378) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldseth_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      let op ← (( do (undefined_MemAtomicOp (← occLabel 4379) ()) ) : SailM MemAtomicOp )
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsmax_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsmin_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsminb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


def decode_ldsminh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
        (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
        (Sail.Int.toNatChecked (t)) tagchecked))


end ArmFull.Functions
