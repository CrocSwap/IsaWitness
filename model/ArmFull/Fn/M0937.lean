import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0041
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0215
import ArmFull.Fn.M0227
import ArmFull.Fn.M0581
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M0855

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

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem
  part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4971)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4972)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool_at (← occLabel 4973) ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let element := (w__0 : (BitVec (2 * esize)))
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (UnsignedSatQ
              (BitVec.toInt element) esize)) ) : SailM ((BitVec esize) × Bool) )
          let w__1 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__2 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__2 27 27 1#1))
          else (pure (()))
          (pure ((element, result, sat)))
      (pure loop_vars)) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4974)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4975) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4976) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 4977) ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let sum : Int := (Int.shiftr ((element1 +i element2) +i 1) 1)
          let w__4 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange sum (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0
  ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_insert_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-arm/instrs64.sail:49719.56-49719.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4978)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  ArmFull.assert (esize ≥b 0) "sail-arm/instrs64.sail:49723.34-49723.35"
  let mask : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth ((Ones (n := (Sail.Int.toNatChecked (esize)))) >>> shift))
  let shifted ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4979)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let (result, shifted) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (result, shifted)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, shifted) := loop_vars
        loop_vars ← do
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "sail-arm/instrs64.sail:49727.198-49727.199"
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let shifted := ((w__0 >>> shift) : (BitVec (Sail.Int.toNatChecked (esize : Int))))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e (Sail.Int.toNatChecked (esize)))) )
            : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let w__2 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked (esize))
              (Sail.BitVec.castWidth ((w__1 &&& (Complement.complement mask)) ||| shifted))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
          let result := (w__2 : (BitVec (Sail.Int.toNatChecked (datasize : Int))))
          (pure ((result, shifted)))
      (pure loop_vars)) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (esize : Int))))
    )
  (V_set d (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Int, elements : Int, esize : Int, k_is_unsigned
  : Bool, n : Nat, k_round : Bool, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_sisd (accumulate : Bool) (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (round : Bool) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-arm/instrs64.sail:49792.56-49792.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4980)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let element ← (( do (undefined_int_at (← occLabel 4981) ()) ) : SailM Int )
  let operand2 ← (( do
    if (accumulate : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (datasize)))))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (datasize))))))) ) :
    SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          ArmFull.assert (esize ≥b 0) "sail-arm/instrs64.sail:49799.38-49799.39"
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "sail-arm/instrs64.sail:49800.179-49800.180"
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e (Sail.Int.toNatChecked (esize)))) ) :
            SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (RShr w__2 shift round) ) : SailM Int )
          let element : Int := (w__3 : Int)
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e (Sail.Int.toNatChecked (esize)))) )
            : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
          let w__5 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked (esize))
              (Sail.BitVec.castWidth (w__4 + (Sail.BitVec.castWidth (integer_subrange element
                  (esize -i 1) 0))))) ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
          let result := (w__5 : (BitVec (Sail.Int.toNatChecked (datasize : Int))))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (Sail.Int.toNatChecked (datasize : Int)))) )
  (V_set d (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, part : Nat, shift : Int, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4982)
      (Sail.Int.toNatChecked ((datasize *i 2))))) ) : SailM (BitVec (datasize * 2)) )
  let element ← (( do (undefined_int_at (← occLabel 4983) ()) ) : SailM Int )
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
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element : Int := ((_shl_int_general w__1 shift) : Int)
          let w__2 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange element ((2 *i esize) -i 1) 0))) ) : SailM
            (BitVec (datasize * 2)) )
          let result := (w__2 : (BitVec (datasize * 2)))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (datasize * 2))) )
  (V_set d (Sail.Int.toNatChecked ((datasize *i 2))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, k_op1_unsigned
  : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem i [0, 1, 2, 3] ∧
  List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (d : Nat) (datasize : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5012)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let res ← (( do
            let loop_b_lower : Nat := 0
            let loop_b_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for b in [loop_b_lower:loop_b_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do (Elem_read operand1 ((4 *i e) +i b) 8) ) : SailM (BitVec 8) )
                  let element1 ← (( do (asl_Int w__0 op1_unsigned) ) : SailM Int )
                  let w__1 ← (( do (Elem_read operand2 ((4 *i i) +i b) 8) ) : SailM (BitVec 8) )
                  let element2 ← (( do (asl_Int w__1 op2_unsigned) ) : SailM Int )
                  let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec 32) )
          (Elem_set result e 32 res)
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5013)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let op1 ← (( do (undefined_int_at (← occLabel 5014) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 5015) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 5016) ()) ) : SailM Bool )
  let (op1, op2, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (op1, op2, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (op1, op2, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 (! is_unsigned)) ) : SailM Int )
          let op1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let op2 : Int := (w__3 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (op1 +i op2) esize
              is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          let w__4 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__5 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__5 27 27 1#1))
          else (pure (()))
          (pure ((op1, op2, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_sysp_aarch64_instrs_system_sysops_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveSysInstr128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) && (Rt != 0b11111#5)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int :=
    if ((t == 31) : Bool)
    then 31
    else (t +i 1)
  let sys_op0 : Nat := 1
  let sys_op1 : Int := (BitVec.toNat op1)
  let sys_op2 : Int := (BitVec.toNat op2)
  let sys_crn : Int := (BitVec.toNat CRn)
  let sys_crm : Int := (BitVec.toNat CRm)
  (execute_aarch64_instrs_system_sysops_128 (Sail.Int.toNatChecked (sys_crm))
    (Sail.Int.toNatChecked (sys_crn)) sys_op0 (Sail.Int.toNatChecked (sys_op1))
    (Sail.Int.toNatChecked (sys_op2)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, k_is_tbl : Bool, m : Nat, n__arg :
  Nat, regs : Nat, List.elem regs [1, 2, 3, 4] ∧
  0 ≤ n__arg ∧
  n__arg ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_table (d : Nat) (datasize : Nat) (elements : Nat) (is_tbl : Bool) (m : Nat) (n__arg : Nat) (regs : Nat) : SailM Unit := do
  let n : Int := n__arg
  (CheckFPAdvSIMDEnabled64 ())
  let indices ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let table : (BitVec (128 * regs)) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((128 *i regs))))))
  let index ← (( do (undefined_int_at (← occLabel 5019) ()) ) : SailM Int )
  let (n, table) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (n, table)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (n, table) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
          let table :=
            ((Sail.BitVec.updateSubrange table (Sail.Int.toNatChecked (((128 *i i) +i 127)))
              (Sail.Int.toNatChecked ((128 *i i))) (Sail.BitVec.castWidth w__0)) : (BitVec (128 * regs)))
          let n : Int := (fmod_int (n +i 1) 32)
          (pure ((n, table)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (128 * regs))) )
  let result ← (( do
    if (is_tbl : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := datasize)))))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read d datasize))) ) : SailM (BitVec datasize) )
  let (index, result) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (index, result)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (index, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (Elem_read indices i 8) ) : SailM (BitVec 8) )
          let index : Int := ((BitVec.toNat w__2) : Int)
          let index : Int := index
          let result ← (( do
            if ((index <b (16 *i regs)) : Bool)
            then
              (do
                let w__3 ← (( do (Elem_read table index 8) ) : SailM (BitVec 8) )
                (Elem_set result i 8 w__3))
            else (pure (result)) ) : SailM (BitVec datasize) )
          (pure ((index, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, pairs : Int, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_transpose (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (pairs : Int) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5020)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, idxdsize : Nat, index : Int, n : Nat, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_move_unsigned (d : Nat) (datasize : Nat) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  if ((index == 0) : Bool)
  then
    (do
      (CheckFPEnabled64 ()))
  else
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n idxdsize)) ) : SailM
    (BitVec idxdsize) )
  ArmFull.assert (datasize ≥b esize) "sail-arm/instrs64.sail:52593.42-52593.43"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand index esize)) ) : SailM
    (BitVec esize) )
  (X_set d datasize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend w__0 datasize)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int (d : Nat) (datasize : Nat) (elements : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5024)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector_at (← occLabel 5025) 32) ) : SailM (BitVec 32) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
          let element := (w__0 : (BitVec 32))
          let w__1 ← (( do (UnsignedRecipEstimate (k_N := 32) element) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_set result e 32 w__1) ) : SailM (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (d : Nat) (datasize : Nat) (elements : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5026)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector_at (← occLabel 5027) 32) ) : SailM (BitVec 32) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
          let element := (w__0 : (BitVec 32))
          let w__1 ← (( do (UnsignedRSqrtEstimate (k_N := 32) element) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_set result e 32 w__1) ) : SailM (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot (d : Nat) (datasize : Nat) (elements : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5028)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let res ← (( do
            let loop_b_lower : Nat := 0
            let loop_b_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for b in [loop_b_lower:loop_b_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do (Elem_read operand1 ((4 *i e) +i b) 8) ) : SailM (BitVec 8) )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do (Elem_read operand2 ((4 *i e) +i b) 8) ) : SailM (BitVec 8) )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec 32) )
          (Elem_set result e 32 res)
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_unzip (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operandl ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operandh ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5029)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let zipped : (BitVec (datasize * 2)) := (Sail.BitVec.castWidth (operandh +++ operandl))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read zipped ((2 *i e) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha3_xar (Sail.Int.toNatChecked (d)) imm6
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem
  part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5030)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5031)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let element := (w__0 : (BitVec (2 * esize)))
          let w__1 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb element
                (Sail.Int.toNatChecked ((esize -i 1))) 0))) ) : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize)) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


end ArmFull.Functions
