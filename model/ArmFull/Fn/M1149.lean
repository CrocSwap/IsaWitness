module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1091
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1128 set_option backward.proofsInPublic true @[expose] public section

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
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) neg))


def decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) neg))


def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) neg))


def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) neg))


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
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
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
      let abs := abs
      let cmp := cmp
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
