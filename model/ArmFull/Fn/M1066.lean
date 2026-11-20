module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0966
public import ArmFull.Fn.M0967 set_option backward.proofsInPublic true @[expose] public section

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

def decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b01#2) || (size == 0b10#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (((size == 0b11#2) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do (HaveBit128PMULLExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let datasize : Nat := 64
          let part : Int := (BitVec.toNat Q)
          let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly
            (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))))


def decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_rbit (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
    (Sail.Int.toNatChecked (n)))


def decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let container_size : Int := 16
      let container_size : Int :=
        match op with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size : Int := container_size
      let containers : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
      let elements_per_container : Int :=
        (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))


def decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let container_size : Int := 16
      let container_size : Int :=
        match op with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size : Int := container_size
      let containers : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
      let elements_per_container : Int :=
        (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))


def decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let container_size : Int := 16
      let container_size : Int :=
        match op with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size : Int := container_size
      let containers : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
      let elements_per_container : Int :=
        (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))


def decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (fdiv_int datasize esize)
      let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
      let round : Bool := (op == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:41451.51-41451.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_logical (Sail.Int.toNatChecked (d)) datasize
        elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift))


def decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (fdiv_int datasize esize)
      let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
      let round : Bool := (op == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:41483.51-41483.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_logical (Sail.Int.toNatChecked (d)) datasize
        elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift))


def decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      let accumulate : Bool := (ac == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      let accumulate : Bool := (ac == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      let accumulate : Bool := (ac == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      let accumulate : Bool := (ac == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let accumulate : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        is_unsigned))


def decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let accumulate : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        is_unsigned))


def decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let accumulate : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        is_unsigned))


def decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let accumulate : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        is_unsigned))


def decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked ((2 *i esize))))
      let acc : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) is_unsigned))


def decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked ((2 *i esize))))
      let acc : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) is_unsigned))


def decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked ((2 *i esize))))
      let acc : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) is_unsigned))


def decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked ((2 *i esize))))
      let acc : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) is_unsigned))


def decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op is_unsigned))


def decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op is_unsigned))


def decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op is_unsigned))


def decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op is_unsigned))


def decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b11#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let datasize : Int :=
            if ((Q == 1#1) : Bool)
            then 128
            else 64
          let elements : Int :=
            (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
          let is_unsigned : Bool := (U == 1#1)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_reduce_add_long (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) is_unsigned)))


end ArmFull.Functions
