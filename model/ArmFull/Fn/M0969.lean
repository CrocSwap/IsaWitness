module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0882 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4855)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4856) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4857)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
  let (element1, product, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, product, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, product, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__2 : Int)
          let product : (BitVec (2 * esize)) :=
            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0))
          let w__3 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth product)) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__3 : (BitVec (2 * datasize)))
          (pure ((element1, product, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4862)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4863) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4864) ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := ((BitVec.toInt w__0) : Int)
          let element : Int :=
            if (neg : Bool)
            then (Neg.neg element)
            else (Int.natAbs element)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ element esize)) ) :
            SailM ((BitVec esize) × Bool) )
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
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4865)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4866) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4867) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 4868) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4869) ()) ) : SailM Bool )
  let (element1, element2, result, sat, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sat, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sat, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let sum : Int := (element1 +i element2)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ sum esize is_unsigned)) )
            : SailM ((BitVec esize) × Bool) )
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
          (pure ((element1, element2, result, sat, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Bool × Int) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let operand3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4870)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4871) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4872)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do (undefined_int_at (← occLabel 4873) ()) ) : SailM Int )
  let sat1 ← (( do (undefined_bool_at (← occLabel 4874) ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool_at (← occLabel 4875) ()) ) : SailM Bool )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toInt w__0)
  let (accum, element1, product, result, sat1, sat2) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accum, element1, product, result, sat1, sat2)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accum, element1, product, result, sat1, sat2) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__1) : Int)
          let w__2 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
              ((2 *i element1) *i element2) (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM
            ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__2 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          let accum ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum : Int := (((BitVec.toInt w__3) -i (BitVec.toInt product)) : Int)
                (pure (accum)))
            else
              (do
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum : Int := (((BitVec.toInt w__4) +i (BitVec.toInt product)) : Int)
                (pure (accum))) ) : SailM Int )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ accum
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let w__5 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth __tup_0)) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__5 : (BitVec (2 * datasize)))
          let sat2 : Bool := __tup_1
          if ((sat1 || sat2) : Bool)
          then
            (do
              let w__6 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__6 27 27 1#1))
          else (pure (()))
          (pure ((accum, element1, product, result, sat1, sat2)))
      (pure loop_vars)) ) : SailM
    (Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool × Bool) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4884)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4885) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4886) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4887)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do (undefined_int_at (← occLabel 4888) ()) ) : SailM Int )
  let sat1 ← (( do (undefined_bool_at (← occLabel 4889) ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool_at (← occLabel 4890) ()) ) : SailM Bool )
  let (accum, element1, element2, product, result, sat1, sat2) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accum, element1, element2, product, result, sat1, sat2)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accum, element1, element2, product, result, sat1, sat2) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__0) : Int)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := ((BitVec.toInt w__1) : Int)
          let w__2 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
              ((2 *i element1) *i element2) (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM
            ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__2 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          let accum ← (( do
            if (sub_op : Bool)
            then
              (do
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum : Int := (((BitVec.toInt w__3) -i (BitVec.toInt product)) : Int)
                (pure (accum)))
            else
              (do
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let accum : Int := (((BitVec.toInt w__4) +i (BitVec.toInt product)) : Int)
                (pure (accum))) ) : SailM Int )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ accum
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM ((BitVec (2 * esize)) × Bool) )
          let w__5 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth __tup_0)) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__5 : (BitVec (2 * datasize)))
          let sat2 : Bool := __tup_1
          if ((sat1 || sat2) : Bool)
          then
            (do
              let w__6 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__6 27 27 1#1))
          else (pure (()))
          (pure ((accum, element1, element2, product, result, sat1, sat2)))
      (pure loop_vars)) ) : SailM
    (Int × Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool × Bool) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_rounding
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4891)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4892) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4893) ()) ) : SailM Int )
  let product ← (( do (undefined_int_at (← occLabel 4894) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4895) ()) ) : SailM Bool )
  let (element1, element2, product, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, product, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, product, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__0) : Int)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := ((BitVec.toInt w__1) : Int)
          let product : Int := ((2 *i element1) *i element2)
          let w__2 ← (( do (RShr product esize rounding) ) : SailM Int )
          let product : Int := (w__2 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ product esize)) ) :
            SailM ((BitVec esize) × Bool) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__4 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__4 27 27 1#1))
          else (pure (()))
          (pure ((element1, element2, product, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4896)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4897) ()) ) : SailM Int )
  let product ← (( do (undefined_int_at (← occLabel 4898) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4899) ()) ) : SailM Bool )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toInt w__0)
  let (element1, product, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, product, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, product, result, sat) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__1) : Int)
          let product : Int := ((2 *i element1) *i element2)
          let w__2 ← (( do (RShr product esize round) ) : SailM Int )
          let product : Int := (w__2 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ product esize)) ) :
            SailM ((BitVec esize) × Bool) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__4 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__4 27 27 1#1))
          else (pure (()))
          (pure ((element1, product, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read m part datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4908)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4909) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4910) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4911)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool_at (← occLabel 4912) ()) ) : SailM Bool )
  let (element1, element2, product, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, product, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, product, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__0) : Int)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := ((BitVec.toInt w__1) : Int)
          let w__2 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
              ((2 *i element1) *i element2) (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM
            ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__2 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          let w__3 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth product)) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__3 : (BitVec (2 * datasize)))
          if (sat : Bool)
          then
            (do
              let w__4 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__4 27 27 1#1))
          else (pure (()))
          (pure ((element1, element2, product, result, sat)))
      (pure loop_vars)) ) : SailM
    (Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Vpart_read n part datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4913)
      (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int_at (← occLabel 4914) ()) ) : SailM Int )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4915)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool_at (← occLabel 4916) ()) ) : SailM Bool )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toInt w__0)
  let (element1, product, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, product, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, product, result, sat) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__1) : Int)
          let w__2 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
              ((2 *i element1) *i element2) (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM
            ((BitVec (2 * esize)) × Bool) )
          let (tup__0, tup__1) := (w__2 : ((BitVec (2 * esize)) × Bool))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          let w__3 ← (( do
            (Elem_set result e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth product)) ) : SailM (BitVec (2 * datasize)) )
          let result := (w__3 : (BitVec (2 * datasize)))
          if (sat : Bool)
          then
            (do
              let w__4 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__4 27 27 1#1))
          else (pure (()))
          (pure ((element1, product, result, sat)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool) )
  (V_set d (Sail.Int.toNatChecked ((2 *i datasize))) (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_rounding
  : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4921)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4922) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4923) ()) ) : SailM Int )
  let element3 ← (( do (undefined_int_at (← occLabel 4924) ()) ) : SailM Int )
  let accum ← (( do (undefined_int_at (← occLabel 4925) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4926) ()) ) : SailM Bool )
  let (accum, element1, element2, element3, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accum, element1, element2, element3, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accum, element1, element2, element3, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__0) : Int)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := ((BitVec.toInt w__1) : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := ((BitVec.toInt w__2) : Int)
          let accum : Int :=
            if (sub_op : Bool)
            then ((Int.shiftl element3 esize) -i (2 *i (element1 *i element2)))
            else ((Int.shiftl element3 esize) +i (2 *i (element1 *i element2)))
          let w__3 ← (( do (RShr accum esize rounding) ) : SailM Int )
          let accum : Int := (w__3 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ accum esize)) ) :
            SailM ((BitVec esize) × Bool) )
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
          (pure ((accum, element1, element2, element3, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


end ArmFull.Functions
