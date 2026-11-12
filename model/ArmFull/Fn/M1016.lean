import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0167
import ArmFull.Fn.M0932

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

def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
    (Sail.Int.toNatChecked (n)))


def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert (0 ≤b (size +i 1)) "sail-arm/instrs64.sail:10486.37-10486.38"
  let index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  let idxdsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 size)
  let datasize : Int := esize
  let elements : Nat := 1
  ArmFull.assert (((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) && ((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256))) "sail-arm/instrs64.sail:10492.101-10492.102"
  (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n)))


def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert (0 ≤b (size +i 1)) "sail-arm/instrs64.sail:10513.37-10513.38"
  let index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  let idxdsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
    then 128
    else 64
  if (((size == 3) && (Q == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 size)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (fdiv_int datasize esize)
  ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-arm/instrs64.sail:10522.58-10522.59"
  (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n)))


def decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 3) && (Q == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 size)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (fdiv_int datasize esize)
  ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-arm/instrs64.sail:10565.58-10565.59"
  (execute_aarch64_instrs_vector_transfer_integer_dup (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((Q == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm4 3)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let position : Int := (Int.shiftl (BitVec.toNat imm4) 3)
  (execute_aarch64_instrs_vector_transfer_vector_extract (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    position)


def decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let imm8 : (BitVec 8) := (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)
  let imm16 : (BitVec 16) :=
    (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)])) +++ (Complement.complement
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])))) +++ (BitVec.replicateBits
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])) 2)) +++ (Sail.BitVec.extractLsb
          imm8 5 0)) +++ (Zeros (n := 6)))
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm16
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 16)))))
  (execute_aarch64_instrs_vector_fp16_movi (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (rd)))


def decode_fmov_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 4285) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then sailThrow ((Error_Undefined ()))
                                                    else (pure (()))
                                                    (pure (ImmediateOp_MOVI)))))))))))))) ) : SailM
    ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (execute_aarch64_instrs_vector_fp16_movi (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (rd)))


def decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert (0 ≤b (size +i 1)) "sail-arm/instrs64.sail:22555.37-22555.38"
  let dst_index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  ArmFull.assert (0 ≤b size) "sail-arm/instrs64.sail:22557.33-22557.34"
  let src_index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 (Sail.Int.toNatChecked (size))))
  let idxdsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm4 3)])) == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (size)))
  match esize with
  | 8 =>
    (do
      match idxdsize with
      | 64 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 8 64 (Sail.Int.toNatChecked (n)) src_index))
      | 128 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 8 128 (Sail.Int.toNatChecked (n)) src_index))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs64.sail:22571.28-22571.29"
          throw Error.Exit))
  | 16 =>
    (do
      match idxdsize with
      | 64 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 16 64 (Sail.Int.toNatChecked (n)) src_index))
      | 128 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 16 128 (Sail.Int.toNatChecked (n)) src_index))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs64.sail:22584.28-22584.29"
          throw Error.Exit))
  | 32 =>
    (do
      match idxdsize with
      | 64 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 32 64 (Sail.Int.toNatChecked (n)) src_index))
      | 128 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 32 128 (Sail.Int.toNatChecked (n)) src_index))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs64.sail:22597.28-22597.29"
          throw Error.Exit))
  | 64 =>
    (do
      match idxdsize with
      | 64 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 64 64 (Sail.Int.toNatChecked (n)) src_index))
      | 128 =>
        (do
          (execute_aarch64_instrs_vector_transfer_vector_insert (Sail.Int.toNatChecked (d))
            dst_index 64 128 (Sail.Int.toNatChecked (n)) src_index))
      | _ =>
        (do
          ArmFull.assert false "sail-arm/instrs64.sail:22610.28-22610.29"
          throw Error.Exit))
  | _ =>
    (do
      ArmFull.assert false "sail-arm/instrs64.sail:22641.22-22641.23"
      throw Error.Exit)


def decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert (0 ≤b (size +i 1)) "sail-arm/instrs64.sail:22677.37-22677.38"
  let index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  let esize : Int := (_shl_int_general 8 size)
  let datasize : Nat := 128
  ArmFull.assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "sail-arm/instrs64.sail:22681.58-22681.59"
  (execute_aarch64_instrs_vector_transfer_integer_insert (Sail.Int.toNatChecked (d)) datasize
    (Sail.Int.toNatChecked (esize)) index (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
