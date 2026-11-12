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
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0840
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

def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let cmp ← (( do (undefined_CompareOp (← occLabel 4136) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4137) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4138) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4139) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4140) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4141) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4142) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4143) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let cmp ← (( do (undefined_CompareOp (← occLabel 4144) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4145) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4146) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4147) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4148) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4149) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4150) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4151) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let cmp ← (( do (undefined_CompareOp (← occLabel 4152) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4153) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4154) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4155) ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (BitVec.setWidth 3 ((E +++ U) +++ ac)) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure ((abs, cmp))))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure ((abs, cmp))))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure ((abs, cmp))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_pair
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4156)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4157)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4158)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let (element1, element2) ← (( do
            if (pair : Bool)
            then
              (do
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat (2 *i e) esize))
                  ) : SailM (BitVec esize) )
                let element1 := (w__0 : (BitVec esize))
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read concat ((2 *i e) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__1 : (BitVec esize))
                (pure ((element1, element2))))
            else
              (do
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 := (w__2 : (BitVec esize))
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__3 : (BitVec esize))
                (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__5 ← (( do (FPAdd element1 element2 w__4) ) : SailM (BitVec esize) )
          let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
            (BitVec datasize) )
          let result := (w__6 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_add_sub (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m esize)) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read n 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let result ← (( do
    if (sub_op : Bool)
    then
      (do
        let w__1 ← (( do (FPSub operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__1))))
    else
      (do
        let w__3 ← (( do (FPAdd operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__3)))) ) :
    SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rot : (BitVec 1)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4159)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4160)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4161)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element3, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
    (do
      let mut loop_vars := (element1, element3, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element3, result) := loop_vars
        loop_vars ← do
          let (element1, element3) ← (( do
            match rot with
            | 0 =>
              (do
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:12690.55-12690.56"
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__1 ← (( do (FPNeg w__0) ) : SailM (BitVec esize) )
                let element1 := (w__1 : (BitVec esize))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let element3 := (w__2 : (BitVec esize))
                (pure ((element1, element3))))
            | _ =>
              (do
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let element1 := (w__3 : (BitVec esize))
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:12696.55-12696.56"
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (FPNeg w__4) ) : SailM (BitVec esize) )
                let element3 := (w__5 : (BitVec esize))
                (pure ((element1, element3)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:12700.49-12700.50"
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) :
            SailM (BitVec esize) )
          let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__8 ← (( do (FPAdd w__6 element1 w__7) ) : SailM (BitVec esize) )
          let w__9 ← (( do (Elem_set result (e *i 2) esize (Sail.BitVec.castWidth w__8)) ) : SailM
            (BitVec datasize) )
          let result := (w__9 : (BitVec datasize))
          let w__10 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__12 ← (( do (FPAdd w__10 element3 w__11) ) : SailM (BitVec esize) )
          let w__13 ← (( do (Elem_set result ((e *i 2) +i 1) esize (Sail.BitVec.castWidth w__12))
            ) : SailM (BitVec datasize) )
          let result := (w__13 : (BitVec datasize))
          (pure ((element1, element3, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_fccmp_float_aarch64_instrs_float_compare_cond (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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


end ArmFull.Functions
