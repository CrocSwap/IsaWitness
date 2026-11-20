module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0226
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
  Nat, m : Nat, n : Nat, k_rounding : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (rounding : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4927)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4928) ()) ) : SailM Int )
  let element3 ← (( do (undefined_int_at (← occLabel 4929) ()) ) : SailM Int )
  let accum ← (( do (undefined_int_at (← occLabel 4930) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4931) ()) ) : SailM Bool )
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
  let element2 : Int := (BitVec.toInt w__0)
  let (accum, element1, element3, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accum, element1, element3, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accum, element1, element3, result, sat) := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := ((BitVec.toInt w__1) : Int)
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
          (pure ((accum, element1, element3, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, k_rounding : Bool, k_saturating : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) (saturating : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4940)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let sat ← (( do (undefined_bool_at (← occLabel 4941) ()) ) : SailM Bool )
  let (result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let shift : Int := (BitVec.toInt (Sail.BitVec.extractLsb w__1 7 0))
          let element ← (( do
            if ((shift ≥b 0) : Bool)
            then
              (let element : Int := (_shl_int_general element shift)
              (pure (element)))
            else
              (do
                let shift : Int := (Neg.neg shift)
                (RShr element shift rounding)) ) : SailM Int )
          let element : Int := element
          if (saturating : Bool)
          then
            (do
              let (__tup_0, __tup_1) ← (( do
                ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ element esize
                  is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
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
              (pure ((result, sat))))
          else
            (do
              let w__5 ← (( do
                (Elem_set result e esize
                  (Sail.BitVec.castWidth (integer_subrange element (esize -i 1) 0))) ) : SailM
                (BitVec datasize) )
              let result := (w__5 : (BitVec datasize))
              (pure ((result, sat))))
      (pure loop_vars)) ) : SailM ((BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, part : Nat, k_round : Bool, shift : Int, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [4, 8, 16, 32, 64] ∧
  List.elem datasize [4, 8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((datasize *i 2))))) ) : SailM
    (BitVec (datasize * 2)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4942)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4943) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4944) ()) ) : SailM Bool )
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
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__2 ← (( do (RShr w__1 shift round) ) : SailM Int )
          let element : Int := (w__2 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ element esize is_unsigned))
            ) : SailM ((BitVec esize) × Bool) )
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
          (pure ((element, result, sat)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, k_round
  : Bool, shift : Int, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [4, 8, 16, 32, 64] ∧
  List.elem datasize [4, 8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((datasize *i 2))))) ) : SailM
    (BitVec (datasize * 2)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4945)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4946) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4947) ()) ) : SailM Bool )
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
          let w__1 ← (( do (RShr (BitVec.toInt w__0) shift round) ) : SailM Int )
          let element : Int := (w__1 : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (UnsignedSatQ element esize)) )
            : SailM ((BitVec esize) × Bool) )
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__3 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__3 27 27 1#1))
          else (pure (()))
          (pure ((element, result, sat)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, k_dst_unsigned : Bool, elements : Int, esize : Nat, n
  : Nat, shift : Int, k_src_unsigned : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [4, 8, 16, 32, 64] ∧
  List.elem datasize [4, 8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_sat_sisd (d : Nat) (datasize : Nat) (dst_unsigned : Bool) (elements : Int) (esize : Nat) (n : Nat) (shift : Int) (src_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:48981.56-48981.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4948)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 4949) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4950) ()) ) : SailM Bool )
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
          let w__1 ← (( do (asl_Int w__0 src_unsigned) ) : SailM Int )
          let element : Int := ((_shl_int_general w__1 shift) : Int)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ element esize dst_unsigned))
            ) : SailM ((BitVec esize) × Bool) )
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__3 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__3 27 27 1#1))
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
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4963)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 4964) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 4965) ()) ) : SailM Int )
  let diff ← (( do (undefined_int_at (← occLabel 4966) ()) ) : SailM Int )
  let sat ← (( do (undefined_bool_at (← occLabel 4967) ()) ) : SailM Bool )
  let (diff, element1, element2, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (diff, element1, element2, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (diff, element1, element2, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let element1 : Int := (w__1 : Int)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__3 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let element2 : Int := (w__3 : Int)
          let diff : Int := (element1 -i element2)
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ diff esize is_unsigned)) )
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
          (pure ((diff, element1, element2, result, sat)))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4968)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4969)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool_at (← occLabel 4970) ()) ) : SailM Bool )
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
          let w__1 ← (( do (asl_Int element is_unsigned) ) : SailM Int )
          let (__tup_0, __tup_1) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ w__1 esize is_unsigned)) )
            : SailM ((BitVec esize) × Bool) )
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth __tup_0)) ) : SailM
            (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          let sat : Bool := __tup_1
          if (sat : Bool)
          then
            (do
              let w__3 ← (( do readReg FPSR ) : SailM (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__3 27 27 1#1))
          else (pure (()))
          (pure ((element, result, sat)))
      (pure loop_vars)) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


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
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:49719.56-49719.57"
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (datasize))))
    ) : SailM (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4978)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  ArmFull.assert (esize ≥b 0) "sail-inputs/15-instrs64.sail:49723.34-49723.35"
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
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "sail-inputs/15-instrs64.sail:49727.198-49727.199"
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
  ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "sail-inputs/15-instrs64.sail:49792.56-49792.57"
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
          ArmFull.assert (esize ≥b 0) "sail-inputs/15-instrs64.sail:49799.38-49799.39"
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "sail-inputs/15-instrs64.sail:49800.179-49800.180"
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


end ArmFull.Functions
