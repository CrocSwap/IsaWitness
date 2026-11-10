import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
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

def decode_cash_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_casp_aarch64_instrs_memory_atomicops_cas_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rs 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize : Int := datasize
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_pair acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) release (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t))
    tagchecked)


/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd (abs : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4104)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4105)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let diff ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4106)
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
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (diff, element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (diff, element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__2 : (BitVec esize))
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__3 : (BitVec esize))
          let w__4 ← (( do (FPSub element1 element2 fpcr) ) : SailM (BitVec esize) )
          let diff := (w__4 : (BitVec esize))
          let w__6 ← (( do
            if (abs : Bool)
            then
              (do
                (FPAbs diff))
            else (pure (diff)) ) : SailM (BitVec esize) )
          let w__7 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__6))) )
            : SailM (BitVec 128) )
          let result := (w__7 : (BitVec 128))
          (pure ((diff, element1, element2, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_unary (d : Nat) (esize : Nat) (fpop : FPUnaryOp) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((bne fpop FPUnaryOp_MOV) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((integer_subrange 0 127 0))) ) : SailM (BitVec 128) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let result ← (( do
    match fpop with
    | .FPUnaryOp_MOV =>
      (do
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth operand))))
    | .FPUnaryOp_ABS =>
      (do
        let w__3 ← (( do (FPAbs operand) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__3))))
    | .FPUnaryOp_NEG =>
      (do
        let w__5 ← (( do (FPNeg operand) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__5))))
    | .FPUnaryOp_SQRT =>
      (do
        let w__7 ← (( do (FPSqrt operand fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__7)))) ) :
    SailM (BitVec 128) )
  (V_set d 128 result)


def decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) neg)


def decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) neg)


def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4116) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4117) ()) ) : SailM Bool )
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


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4118) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4119) ()) ) : SailM Bool )
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


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4120) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4121) ()) ) : SailM Bool )
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


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4122) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4123) ()) ) : SailM Bool )
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


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4124) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4125) ()) ) : SailM Bool )
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


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4126) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4127) ()) ) : SailM Bool )
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


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4128) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4129) ()) ) : SailM Bool )
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


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp (← occLabel 4130) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4131) ()) ) : SailM Bool )
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


def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4132) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4133) ()) ) : SailM Bool )
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


def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let cmp ← (( do (undefined_CompareOp (← occLabel 4134) ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool_at (← occLabel 4135) ()) ) : SailM Bool )
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


end ArmFull.Functions
