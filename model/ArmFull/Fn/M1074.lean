import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0023
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1040

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

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, k_floating_point
  : Bool, m : Nat, regs : Int, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABS_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3342) ()) ) : SailM Int )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let result ← (( do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Int := (regs -i 1)
        (do
          let mut loop_vars := result
          for r in [loop_r_lower:loop_r_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let loop_e_lower : Nat := 0
              let loop_e_upper : Int := (elements -i 1)
              (do
                let mut loop_vars_1 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_1
                  loop_vars_1 ← do
                    if (floating_point : Bool)
                    then
                      (do
                        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:19798.61-19798.62"
                        let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) )
                          : SailM (BitVec esize) )
                        let w__3 ← (( do (FPAbs w__2) ) : SailM (BitVec esize) )
                        let w__4 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                            (Sail.BitVec.castWidth w__3))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__4)
                        (pure (result)))
                    else
                      (do
                        let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e esize)) )
                          : SailM (BitVec esize) )
                        let result : Int := ((Int.natAbs (BitVec.toInt w__6)) : Int)
                        let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__8 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e esize
                            (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) :
                          SailM (BitVec 64) )
                        (D_set (d +i r) w__8)
                        (pure (result)))
                (pure loop_vars_1))
          (pure loop_vars)) ) : SailM Int )
      (pure (())))
  else
    (do
      match esize with
      | 16 =>
        (do
          let w__9 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPAbs (Sail.BitVec.extractLsb w__9 15 0)) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__10)))
      | 32 =>
        (do
          let w__11 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__12 ← (( do (FPAbs w__11) ) : SailM (BitVec 32) )
          (S_set d w__12))
      | 64 =>
        (do
          let w__13 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__14 ← (( do (FPAbs w__13) ) : SailM (BitVec 64) )
          (D_set d w__14))
      | _ => (pure (())))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, k_or_equal : Bool, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VACGE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (or_equal : Bool) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3353)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3354)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (FPAbs w__1) ) : SailM (BitVec esize) )
                let op1 := (w__2 : (BitVec esize))
                let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (FPAbs w__4) ) : SailM (BitVec esize) )
                let op2 := (w__5 : (BitVec esize))
                let test_passed ← (( do (undefined_bool_at (← occLabel 3355) ()) ) : SailM Bool
                  )
                let test_passed ← (( do
                  if (or_equal : Bool)
                  then
                    (do
                      let w__6 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      (FPCompareGE op1 op2 w__6))
                  else
                    (do
                      let w__8 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      (FPCompareGT op1 op2 w__8)) ) : SailM Bool )
                let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__11 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                    (Sail.BitVec.castWidth (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__11)
                (pure ((op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCEQ_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let test_passed ← (( do (undefined_bool_at (← occLabel 3369) ()) ) : SailM Bool )
              let test_passed ← (( do
                if (floating_point : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21029.57-21029.58"
                    let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM
                      (BitVec esize) )
                    let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ w__1 zero w__2))
                else
                  (do
                    let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                      SailM (BitVec esize) )
                    let test_passed :=
                      ((w__5 == (Sail.BitVec.castWidth (Zeros (n := esize)))) : Bool)
                    (pure (test_passed))) ) : SailM Bool )
              let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__7 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                  (Sail.BitVec.castWidth (if (test_passed : Bool)
                  then (Ones (n := esize))
                  else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__7)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_int_operation : Bool, m : Nat, n
  : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCEQ_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (int_operation : Bool) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3370)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3371)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let test_passed ← (( do (undefined_bool_at (← occLabel 3372) ()) ) : SailM Bool
                  )
                let test_passed ← (( do
                  if (int_operation : Bool)
                  then
                    (let test_passed : Bool := (op1 == op2)
                    (pure (test_passed)))
                  else
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21135.57-21135.58"
                      let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      (FPCompareEQ op1 op2 w__4)) ) : SailM Bool )
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGE_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let test_passed ← (( do (undefined_bool_at (← occLabel 3373) ()) ) : SailM Bool )
              let test_passed ← (( do
                if (floating_point : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21324.57-21324.58"
                    let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM
                      (BitVec esize) )
                    let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    (FPCompareGE w__1 zero w__2))
                else
                  (do
                    let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                      SailM (BitVec esize) )
                    let test_passed := (((BitVec.toInt w__5) ≥b 0) : Bool)
                    (pure (test_passed))) ) : SailM Bool )
              let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__7 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                  (Sail.BitVec.castWidth (if (test_passed : Bool)
                  then (Ones (n := esize))
                  else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__7)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGE_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (vtype : VCGEType) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3374)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3375)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let test_passed ← (( do (undefined_bool_at (← occLabel 3376) ()) ) : SailM Bool
                  )
                let test_passed ← (( do
                  match vtype with
                  | .VCGEType_signed =>
                    (let test_passed : Bool := ((BitVec.toInt op1) ≥b (BitVec.toInt op2))
                    (pure (test_passed)))
                  | .VCGEType_unsigned =>
                    (let test_passed : Bool := ((BitVec.toNat op1) ≥b (BitVec.toNat op2))
                    (pure (test_passed)))
                  | .VCGEType_fp =>
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21435.59-21435.60"
                      let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      (FPCompareGE op1 op2 w__4)) ) : SailM Bool )
                let test_passed := test_passed
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGT_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let test_passed ← (( do (undefined_bool_at (← occLabel 3377) ()) ) : SailM Bool )
              let test_passed ← (( do
                if (floating_point : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21630.57-21630.58"
                    let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM
                      (BitVec esize) )
                    let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    (FPCompareGT w__1 zero w__2))
                else
                  (do
                    let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                      SailM (BitVec esize) )
                    let test_passed := (((BitVec.toInt w__5) >b 0) : Bool)
                    (pure (test_passed))) ) : SailM Bool )
              let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__7 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                  (Sail.BitVec.castWidth (if (test_passed : Bool)
                  then (Ones (n := esize))
                  else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__7)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGT_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (vtype : VCGTtype) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3378)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3379)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let test_passed ← (( do (undefined_bool_at (← occLabel 3380) ()) ) : SailM Bool
                  )
                let test_passed ← (( do
                  match vtype with
                  | .VCGTtype_signed =>
                    (let test_passed : Bool := ((BitVec.toInt op1) >b (BitVec.toInt op2))
                    (pure (test_passed)))
                  | .VCGTtype_unsigned =>
                    (let test_passed : Bool := ((BitVec.toNat op1) >b (BitVec.toNat op2))
                    (pure (test_passed)))
                  | .VCGTtype_fp =>
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21741.59-21741.60"
                      let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      (FPCompareGT op1 op2 w__4)) ) : SailM Bool )
                let test_passed := test_passed
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLE_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let test_passed ← (( do (undefined_bool_at (← occLabel 3381) ()) ) : SailM Bool )
              let test_passed ← (( do
                if (floating_point : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:21936.57-21936.58"
                    let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM
                      (BitVec esize) )
                    let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    (FPCompareGE zero w__1 w__2))
                else
                  (do
                    let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                      SailM (BitVec esize) )
                    let test_passed := (((BitVec.toInt w__5) ≤b 0) : Bool)
                    (pure (test_passed))) ) : SailM Bool )
              let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__7 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                  (Sail.BitVec.castWidth (if (test_passed : Bool)
                  then (Ones (n := esize))
                  else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__7)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLT_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let test_passed ← (( do (undefined_bool_at (← occLabel 3382) ()) ) : SailM Bool )
              let test_passed ← (( do
                if (floating_point : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs32.sail:22112.57-22112.58"
                    let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM
                      (BitVec esize) )
                    let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    (FPCompareGT zero w__1 w__2))
                else
                  (do
                    let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                      SailM (BitVec esize) )
                    let test_passed := (((BitVec.toInt w__5) <b 0) : Bool)
                    (pure (test_passed))) ) : SailM Bool )
              let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__7 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                  (Sail.BitVec.castWidth (if (test_passed : Bool)
                  then (Ones (n := esize))
                  else (Zeros (n := esize)))))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__7)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, esize : Nat, m : Int, k_quiet_nan_exc : Bool, k_with_zero : Bool, List.elem
  esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCMP_Op_A_txt (d : Nat) (esize : Nat) (m : Int) (quiet_nan_exc : Bool) (with_zero : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3383) 4) ) : SailM (BitVec 4) )
  let nzcv ← (( do
    match esize with
    | 16 =>
      (do
        let op16 ← (( do
          if (with_zero : Bool)
          then
            (do
              (FPZero 0#1 16))
          else
            (do
              let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
        let w__2 ← (( do (S_read d) ) : SailM (BitVec 32) )
        let w__3 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
        (FPCompare (Sail.BitVec.extractLsb w__2 15 0) op16 quiet_nan_exc w__3))
    | 32 =>
      (do
        let op32 ← (( do
          if (with_zero : Bool)
          then
            (do
              (FPZero 0#1 32))
          else
            (do
              (S_read m)) ) : SailM (BitVec 32) )
        let w__7 ← (( do (S_read d) ) : SailM (BitVec 32) )
        let w__8 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
        (FPCompare w__7 op32 quiet_nan_exc w__8))
    | 64 =>
      (do
        let op64 ← (( do
          if (with_zero : Bool)
          then
            (do
              (FPZero 0#1 64))
          else
            (do
              (D_read m)) ) : SailM (BitVec 64) )
        let w__12 ← (( do (D_read d) ) : SailM (BitVec 64) )
        let w__13 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
        (FPCompare w__12 op64 quiet_nan_exc w__13))
    | _ => (pure (nzcv)) ) : SailM (BitVec 4) )
  let w__15 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  (FPSCR_write (Mk_FPSCR_Type (Sail.BitVec.updateSubrange w__15 31 28 nzcv)))


end ArmFull.Functions
