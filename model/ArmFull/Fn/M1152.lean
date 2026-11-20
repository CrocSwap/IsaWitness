module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1128
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
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:13623.55-13623.56"
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
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:13630.55-13630.56"
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
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:13639.55-13639.56"
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
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/15-instrs64.sail:13648.49-13648.50"
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


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
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
      let datasize : Int := esize
      let elements : Nat := 1
      let comparison : CompareOp := CompareOp_LT
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n))))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison : CompareOp := CompareOp_LT
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
      let comparison : CompareOp := CompareOp_LT
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n))))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let comparison : CompareOp := CompareOp_LT
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))))


def decode_fcmp_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ())))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let datasize : Int := datasize
  let signal_all_nans : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) signal_all_nans)


def decode_fcmpe_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ())))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let datasize : Int := datasize
  let signal_all_nans : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) signal_all_nans)


/-- Type quantifiers: d : Nat, dstsize : Nat, n : Nat, srcsize : Nat, List.elem srcsize [16, 32, 64]
  ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem dstsize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_fp (d : Nat) (dstsize : Nat) (n : Nat) (srcsize : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n srcsize)) ) : SailM (BitVec srcsize)
    )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (FPConvert__1 operand fpcr dstsize)) ) : SailM
    (BitVec dstsize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 dstsize (Sail.BitVec.castWidth w__1))) ) :
    SailM (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
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
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
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
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
      let rounding : FPRounding := FPRounding_TIEAWAY
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtas_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4199) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4200) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4201) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else (pure (128)))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__1 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__3 ← (( do (FPRoundingMode w__2) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            let (op, part) ← (( do
              if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 0
                (pure ((op, part)))) ) : SailM (FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            let (fltsize, op, part) ← (( do
              if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let op : FPConvOp :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
                  then FPConvOp_MOV_ItoF
                  else FPConvOp_MOV_FtoI
                let part : Int := 1
                let fltsize : Int := 64
                (pure ((fltsize, op, part)))) ) : SailM (Int × FPConvOp × Int) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__4 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            let (is_unsigned, op, rounding) ← (( do
              if ((! w__4) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let rounding : FPRounding := FPRounding_ZERO
                let is_unsigned : Bool :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                (pure ((is_unsigned, op, rounding)))) ) : SailM (Bool × FPConvOp × FPRounding) )
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "sail-inputs/15-instrs64.sail:14400.22-14400.23"
      throw Error.Exit)


end ArmFull.Functions
