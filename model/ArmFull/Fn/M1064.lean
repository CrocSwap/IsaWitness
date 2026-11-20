module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0965 set_option backward.proofsInPublic true @[expose] public section

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

def decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
      let comparison ← (( do (undefined_CompareOp (← occLabel 4036) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let comparison ← (( do (undefined_CompareOp (← occLabel 4037) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
      let comparison ← (( do (undefined_CompareOp (← occLabel 4038) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let comparison ← (( do (undefined_CompareOp (← occLabel 4039) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
      let comparison ← (( do (undefined_CompareOp (← occLabel 4040) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let comparison ← (( do (undefined_CompareOp (← occLabel 4041) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
      let comparison ← (( do (undefined_CompareOp (← occLabel 4042) ()) ) : SailM CompareOp )
      let comparison : CompareOp :=
        match (BitVec.setWidth 2 (op +++ U)) with
        | 0b00 => CompareOp_GT
        | 0b01 => CompareOp_GE
        | 0b10 => CompareOp_EQ
        | _ => CompareOp_LE
      let comparison := comparison
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let and_test : Bool := (U == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let and_test : Bool := (U == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let and_test : Bool := (U == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let and_test : Bool := (U == 0#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let is_unsigned : Bool := (U == 1#1)
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let is_unsigned : Bool := (U == 1#1)
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let is_unsigned : Bool := (U == 1#1)
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let is_unsigned : Bool := (U == 1#1)
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let cmp_eq : Bool := (eq == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let comparison : CompareOp := CompareOp_LT
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
      let comparison : CompareOp := CompareOp_LT
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b00#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 8
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cnt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
        (Sail.Int.toNatChecked (n))))


def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      ArmFull.assert (0 ≤b (size +i 1)) "sail-inputs/15-instrs64.sail:10486.37-10486.38"
      let index : Int :=
        (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
      let idxdsize : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
        then 128
        else 64
      let esize : Int := (_shl_int_general 8 size)
      let datasize : Int := esize
      let elements : Nat := 1
      ArmFull.assert (((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) && ((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256))) "sail-inputs/15-instrs64.sail:10492.101-10492.102"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n))))


def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      ArmFull.assert (0 ≤b (size +i 1)) "sail-inputs/15-instrs64.sail:10513.37-10513.38"
      let index : Int :=
        (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
      let idxdsize : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
        then 128
        else 64
      if (((size == 3) && (Q == 0#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (_shl_int_general 8 size)
          let datasize : Int :=
            if ((Q == 1#1) : Bool)
            then 128
            else 64
          let elements : Int := (fdiv_int datasize esize)
          ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-inputs/15-instrs64.sail:10522.58-10522.59"
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n)))))


end ArmFull.Functions
