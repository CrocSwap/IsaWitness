import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0118
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
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

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, k_minimum :
  Bool, n : Nat, k_pair : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4269)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4270)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4271)
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
          let result ← (( do
            if (minimum : Bool)
            then
              (do
                let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__5 ← (( do (FPMinNum element1 element2 w__4) ) : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__5)))
            else
              (do
                let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__8 ← (( do (FPMaxNum element1 element2 w__7) ) : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__8))) ) : SailM (BitVec datasize)
            )
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4272)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
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
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__2 : (BitVec esize))
          let element1 ← (( do
            if (sub_op : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let w__5 ← (( do (FPMulAdd w__4 element1 element2 fpcr) ) : SailM (BitVec esize) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__5))) )
            : SailM (BitVec 128) )
          let result := (w__6 : (BitVec 128))
          (pure ((element1, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4277)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4278)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4279)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let element1 ← (( do
            if (sub_op : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__5 ← (( do (FPMulAdd w__3 element1 element2 w__4) ) : SailM (BitVec esize) )
          let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
            (BitVec datasize) )
          let result := (w__6 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n
  : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Vpart_read n part (Sail.Int.toNatChecked ((Int.ediv datasize 2)))))
    ) : SailM (BitVec (datasize / 2)) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4280)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4281)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let (element1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 := (w__0 : (BitVec (esize / 2)))
          let element1 ← (( do
            if (sub_op : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec 32) )
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) w__2
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__3)) ) : SailM
            (BitVec 32) )
          let w__5 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__4)) ) : SailM
            (BitVec datasize) )
          let result := (w__5 : (BitVec datasize))
          (pure ((element1, result)))
      (pure loop_vars)) ) : SailM ((BitVec (esize / 2)) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Vpart_read n part (Sail.Int.toNatChecked ((Int.ediv datasize 2)))))
    ) : SailM (BitVec (datasize / 2)) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Vpart_read m part (Sail.Int.toNatChecked ((Int.ediv datasize 2)))))
    ) : SailM (BitVec (datasize / 2)) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4282)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4283)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4284)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 := (w__0 : (BitVec (esize / 2)))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 := (w__1 : (BitVec (esize / 2)))
          let element1 ← (( do
            if (sub_op : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec 32) )
          let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) w__3
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__4)) ) : SailM
            (BitVec 32) )
          let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
            (BitVec datasize) )
          let result := (w__6 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4286)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4287)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4288)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMul element1 element2 w__2) ) : SailM (BitVec esize) )
          let w__4 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__3)) ) : SailM
            (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_negated : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_mul_product (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (negated : Bool) : SailM Unit := do
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
  let product ← (( do (FPMul operand1 operand2 fpcr) ) : SailM (BitVec esize) )
  let product ← (( do
    if (negated : Bool)
    then
      (do
        (FPNeg product))
    else (pure (product)) ) : SailM (BitVec esize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth product))) ) :
    SailM (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index :
  Nat, m : Nat, k_mulx_op : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem idxdsize [64, 128] ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (mulx_op : Bool) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m idxdsize)) ) : SailM
    (BitVec idxdsize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4289)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index esize)) ) : SailM
    (BitVec esize) )
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
  let (element1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__2 : (BitVec esize))
          let result ← (( do
            if (mulx_op : Bool)
            then
              (do
                let w__3 ← (( do (FPMulX element1 element2 fpcr) ) : SailM (BitVec esize) )
                ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))))
            else
              (do
                let w__5 ← (( do (FPMul element1 element2 fpcr) ) : SailM (BitVec esize) )
                ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__5))))
            ) : SailM (BitVec 128) )
          (pure ((element1, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4294)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4295)
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
          let w__4 ← (( do (FPMulX element1 element2 fpcr) ) : SailM (BitVec esize) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__4))) )
            : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4297)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4298)
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
          let w__4 ← (( do (FPRecipStepFused element1 element2) ) : SailM (BitVec esize) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__4))) )
            : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


end ArmFull.Functions
