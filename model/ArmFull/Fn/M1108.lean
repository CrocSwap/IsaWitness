import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0145
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1040
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072
import ArmFull.Fn.M1078

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

def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then
    (do
      (CheckFPEnabled64 ()))
  else
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4325)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4326)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read n 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__2 : (BitVec esize))
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__3 : (BitVec esize))
          let w__4 ← (( do (FPRSqrtStepFused element1 element2) ) : SailM (BitVec esize) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__4))) )
            : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4327)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4328)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (FPSqrt element w__1) ) : SailM (BitVec esize) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__2)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (abs : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4329)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4330)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let diff ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4331)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4332)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (diff, element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (diff, element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let w__2 ← (( do (FPSub element1 element2 fpcr) ) : SailM (BitVec esize) )
          let diff := (w__2 : (BitVec esize))
          let w__4 ← (( do
            if (abs : Bool)
            then
              (do
                (FPAbs diff))
            else (pure (diff)) ) : SailM (BitVec esize) )
          let w__5 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__4)) ) : SailM
            (BitVec datasize) )
          let result := (w__5 : (BitVec datasize))
          (pure ((diff, element1, element2, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_ld64b_aarch64_instrs_memory_atomicops_ld_acc (Rt : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatLS64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb Rt 4 3)) == 0b11#2) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             Rt 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64b
  (execute_aarch64_instrs_memory_atomicops_ld_acc lst memop (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldadd_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4368) ()) ) : SailM MemAtomicOp )
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


def decode_ldaddb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let op ← (( do (undefined_MemAtomicOp (← occLabel 4369) ()) ) : SailM MemAtomicOp )
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


def decode_ldaddh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldclr_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldclrb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldclrh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldeor_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldeorb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldeorh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldset_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldsetb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldseth_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_memory_atomicops_ld acquire (Sail.Int.toNatChecked (datasize)) is_load
    (Sail.Int.toNatChecked (n)) op regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


end ArmFull.Functions
