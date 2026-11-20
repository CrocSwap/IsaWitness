module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0970 set_option backward.proofsInPublic true @[expose] public section

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

def decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
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
      let rounding : Bool := (R == 1#1)
      let saturating : Bool := (S == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding saturating is_unsigned))


def decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
          let datasize : Int := esize
          let elements : Nat := 1
          let part : Nat := 0
          let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
          let round : Bool := (op == 1#1)
          let is_unsigned : Bool := (U == 1#1)
          ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "sail-inputs/15-instrs64.sail:48572.87-48572.88"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) part round shift is_unsigned)))


def decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let is_unsigned : Bool := (U == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:48605.51-48605.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
        datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift is_unsigned))


def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
          let datasize : Int := esize
          let elements : Nat := 1
          let part : Nat := 0
          let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
          let round : Bool := (op == 1#1)
          let is_unsigned : Bool := (U == 1#1)
          ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "sail-inputs/15-instrs64.sail:48639.87-48639.88"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) part round shift is_unsigned)))


def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let is_unsigned : Bool := (U == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:48672.51-48672.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
        datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift is_unsigned))


def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
          let datasize : Int := esize
          let elements : Nat := 1
          let part : Nat := 0
          let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
          let round : Bool := (op == 1#1)
          let is_unsigned : Bool := (U == 1#1)
          ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "sail-inputs/15-instrs64.sail:48706.87-48706.88"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) part round shift is_unsigned)))


def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let is_unsigned : Bool := (U == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:48739.51-48739.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
        datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift is_unsigned))


def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
          let datasize : Int := esize
          let elements : Nat := 1
          let part : Nat := 0
          let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
          let round : Bool := (op == 1#1)
          let is_unsigned : Bool := (U == 1#1)
          ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "sail-inputs/15-instrs64.sail:48773.87-48773.88"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) part round shift is_unsigned)))


def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let is_unsigned : Bool := (U == 1#1)
      ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:48806.51-48806.52"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
        datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (part)) round shift is_unsigned))


def decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
          let datasize : Int := esize
          let elements : Nat := 1
          let part : Nat := 0
          let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
          let round : Bool := (op == 1#1)
          ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "sail-inputs/15-instrs64.sail:48866.87-48866.88"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd
            (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) part round shift)))


end ArmFull.Functions
