import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0852
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1077

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

def decode_fccmpe_float_aarch64_instrs_float_compare_cond (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize : Int := datasize
  let signal_all_nans : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_float_compare_cond condition (Sail.Int.toNatChecked (datasize)) flags
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) signal_all_nans)


def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4165) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4166) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let comparison ← (( do (undefined_CompareOp (← occLabel 4167) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4168) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4169) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4170) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let comparison ← (( do (undefined_CompareOp (← occLabel 4171) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4172) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4173) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4174) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let comparison ← (( do (undefined_CompareOp (← occLabel 4175) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4176) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4177) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4178) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let comparison ← (( do (undefined_CompareOp (← occLabel 4179) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4180) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rot : (BitVec 2)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4181)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4182)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4183)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4184)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element4 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4185)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let (element1, element2, element3, element4, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
    (do
      let mut loop_vars := (element1, element2, element3, element4, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, element3, element4, result) := loop_vars
        loop_vars ← do
          let (element1, element2, element3, element4) ← (( do
            match rot with
            | 0b00 =>
              (do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element1 := (w__0 : (BitVec esize))
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__1 : (BitVec esize))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element3 := (w__2 : (BitVec esize))
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element4 := (w__3 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | 0b01 =>
              (do
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13536.55-13536.56"
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__5 ← (( do (FPNeg w__4) ) : SailM (BitVec esize) )
                let element1 := (w__5 : (BitVec esize))
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__6 : (BitVec esize))
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element3 := (w__7 : (BitVec esize))
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element4 := (w__8 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | 0b10 =>
              (do
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13543.55-13543.56"
                let w__9 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__10 ← (( do (FPNeg w__9) ) : SailM (BitVec esize) )
                let element1 := (w__10 : (BitVec esize))
                let w__11 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__11 : (BitVec esize))
                let w__12 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__13 ← (( do (FPNeg w__12) ) : SailM (BitVec esize) )
                let element3 := (w__13 : (BitVec esize))
                let w__14 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element4 := (w__14 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | _ =>
              (do
                let w__15 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element1 := (w__15 : (BitVec esize))
                let w__16 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__16 : (BitVec esize))
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13552.55-13552.56"
                let w__17 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__18 ← (( do (FPNeg w__17) ) : SailM (BitVec esize) )
                let element3 := (w__18 : (BitVec esize))
                let w__19 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element4 := (w__19 : (BitVec esize))
                (pure ((element1, element2, element3, element4)))) ) : SailM
            ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13557.49-13557.50"
          let w__20 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 (e *i 2) esize)) ) :
            SailM (BitVec esize) )
          let w__21 ← (( do (FPMulAdd w__20 element2 element1 fpcr) ) : SailM (BitVec esize) )
          let w__22 ← (( do (Elem_set result (e *i 2) esize (Sail.BitVec.castWidth w__21)) ) :
            SailM (BitVec datasize) )
          let result := (w__22 : (BitVec datasize))
          let w__23 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((e *i 2) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let w__24 ← (( do (FPMulAdd w__23 element4 element3 fpcr) ) : SailM (BitVec esize) )
          let w__25 ← (( do (Elem_set result ((e *i 2) +i 1) esize (Sail.BitVec.castWidth w__24))
            ) : SailM (BitVec datasize) )
          let result := (w__25 : (BitVec datasize))
          (pure ((element1, element2, element3, element4, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (rot : (BitVec 2)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4186)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4187)
              (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4188)
              (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
          let element3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4189)
              (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
          let element4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4190)
              (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
          let (element1, element2, element3, element4) ← (( do
            match rot with
            | 0b00 =>
              (do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element1 := (w__0 : (BitVec esize))
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__1 : (BitVec esize))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element3 := (w__2 : (BitVec esize))
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element4 := (w__3 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | 0b01 =>
              (do
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13623.55-13623.56"
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__5 ← (( do (FPNeg w__4) ) : SailM (BitVec esize) )
                let element1 := (w__5 : (BitVec esize))
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__6 : (BitVec esize))
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element3 := (w__7 : (BitVec esize))
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element4 := (w__8 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | 0b10 =>
              (do
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13630.55-13630.56"
                let w__9 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__10 ← (( do (FPNeg w__9) ) : SailM (BitVec esize) )
                let element1 := (w__10 : (BitVec esize))
                let w__11 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__11 : (BitVec esize))
                let w__12 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__13 ← (( do (FPNeg w__12) ) : SailM (BitVec esize) )
                let element3 := (w__13 : (BitVec esize))
                let w__14 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element4 := (w__14 : (BitVec esize))
                (pure ((element1, element2, element3, element4))))
            | _ =>
              (do
                let w__15 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((index *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element1 := (w__15 : (BitVec esize))
                let w__16 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__16 : (BitVec esize))
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13639.55-13639.56"
                let w__17 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (index *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__18 ← (( do (FPNeg w__17) ) : SailM (BitVec esize) )
                let element3 := (w__18 : (BitVec esize))
                let w__19 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element4 := (w__19 : (BitVec esize))
                (pure ((element1, element2, element3, element4)))) ) : SailM
            ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
          let element4 := element4
          let element3 := element3
          let element2 := element2
          let element1 := element1
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:13648.49-13648.50"
          let w__20 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 (e *i 2) esize)) ) :
            SailM (BitVec esize) )
          let w__21 ← (( do (FPMulAdd w__20 element2 element1 fpcr) ) : SailM (BitVec esize) )
          let w__22 ← (( do (Elem_set result (e *i 2) esize (Sail.BitVec.castWidth w__21)) ) :
            SailM (BitVec datasize) )
          let result := (w__22 : (BitVec datasize))
          let w__23 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((e *i 2) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let w__24 ← (( do (FPMulAdd w__23 element4 element3 fpcr) ) : SailM (BitVec esize) )
          (Elem_set result ((e *i 2) +i 1) esize (Sail.BitVec.castWidth w__24))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


end ArmFull.Functions
