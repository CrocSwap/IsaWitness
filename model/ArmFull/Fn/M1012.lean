import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0041
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925

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

/-- Type quantifiers: containers : Int, d : Nat, elements_per_container : Int, esize : Nat, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VREV16_Op_A_txt (containers : Int) (d : Nat) (elements_per_container : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector_at (← occLabel 3711) 64) ) : SailM (BitVec 64) )
  let element ← (( do (undefined_int_at (← occLabel 3712) ()) ) : SailM Int )
  let rev_element ← (( do (undefined_int_at (← occLabel 3713) ()) ) : SailM Int )
  let (element, result, rev_element) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (element, result, rev_element)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (element, result, rev_element) := loop_vars
        loop_vars ← do
          let element : Int := 0
          let (element, result, rev_element) ← (( do
            let loop_c_lower : Nat := 0
            let loop_c_upper : Int := (containers -i 1)
            (do
              let mut loop_vars_1 := (element, result, rev_element)
              for c in [loop_c_lower:loop_c_upper:1]i do
                let (element, result, rev_element) := loop_vars_1
                loop_vars_1 ← do
                  let rev_element : Int := ((element +i elements_per_container) -i 1)
                  let loop_e_lower : Nat := 0
                  let loop_e_upper : Int := (elements_per_container -i 1)
                  (do
                    let mut loop_vars_2 := (element, result, rev_element)
                    for e in [loop_e_lower:loop_e_upper:1]i do
                      let (element, result, rev_element) := loop_vars_2
                      loop_vars_2 ← do
                        let rev_element : Int := rev_element
                        let element : Int := element
                        let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                        let w__1 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 element esize)) ) : SailM
                          (BitVec esize) )
                        let w__2 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set result rev_element esize
                            (Sail.BitVec.castWidth w__1))) ) : SailM (BitVec 64) )
                        let result := (w__2 : (BitVec 64))
                        let element : Int := (element +i 1)
                        let rev_element : Int := (rev_element -i 1)
                        (pure ((element, result, rev_element)))
                    (pure loop_vars_2))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 64) × Int) )
          (D_set (d +i r) result)
          (pure ((element, result, rev_element)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 64) × Int) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRHADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3714) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 3715) ()) ) : SailM Int )
  let result ← (( do (undefined_int_at (← occLabel 3716) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let op1 : Int := (w__2 : Int)
                let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
                let op2 : Int := (w__5 : Int)
                let result : Int := (Int.shiftr ((op1 +i op2) +i 1) 1)
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, op2, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int × Int) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_int_at (← occLabel 3717) ()) ) : SailM Int )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
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
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let shift : Int := (BitVec.toInt (Sail.BitVec.extractLsb w__3 7 0))
                let result : Int :=
                  if ((shift ≥b 0) : Bool)
                  then (_shl_int_general element shift)
                  else
                    (let shift : Int := (Neg.neg shift)
                    (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, shift_amount : Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHR_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3718) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (RShr w__2 shift_amount round) ) : SailM Int )
                let result : Int := (w__3 : Int)
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, 0 ≤
  m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHRN_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3721) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (RShr (BitVec.toNat w__1) shift_amount round) ) : SailM Int )
          let result : Int := (w__2 : Int)
          let w__3 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e esize
              (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
            (BitVec 64) )
          (D_set d w__4)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, shift_amount : Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSRA_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3724) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (RShr w__2 shift_amount round) ) : SailM Int )
                let result : Int := (w__3 : Int)
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e esize)) ) : SailM
                  (BitVec esize) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth (BitVec.addInt w__6 result)))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSUBHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3727) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__4 ← (( do (RShr (BitVec.toNat (w__1 - w__3)) esize round) ) : SailM Int )
          let result : Int := (w__4 : Int)
          let w__5 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__5 e esize
              (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
            (BitVec 64) )
          (D_set d w__6)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount :
  Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHL_i_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
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
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (w__2 <<< shift_amount)))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__3)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, shift_amount
  : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHLL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3730) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let result : Int := ((_shl_int_general w__2 shift_amount) : Int)
          let w__3 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange result ((2 *i esize) -i 1) 0)))) ) : SailM
            (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__4)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHL_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let shift ← (( do (undefined_int_at (← occLabel 3733) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let shift ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := shift
      for r in [loop_r_lower:loop_r_upper:1]i do
        let shift := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := shift
            for e in [loop_e_lower:loop_e_upper:1]i do
              let shift := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let shift : Int := ((BitVec.toInt (Sail.BitVec.extractLsb w__1 7 0)) : Int)
                let result ← (( do (undefined_int_at (← occLabel 3734) ()) ) : SailM Int )
                let result ← (( do
                  if ((shift ≥b 0) : Bool)
                  then
                    (do
                      let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) :
                        SailM (BitVec esize) )
                      let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                      let result : Int := ((_shl_int_general w__4 shift) : Int)
                      (pure (result)))
                  else
                    (do
                      let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e esize)) ) :
                        SailM (BitVec esize) )
                      let w__7 ← (( do (asl_Int w__6 is_unsigned) ) : SailM Int )
                      let result : Int := ((_shr_int_general w__7 (Neg.neg shift)) : Int)
                      (pure (result))) ) : SailM Int )
                let result : Int := result
                let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__9 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                    (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__9)
                (pure (shift))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, shift_amount : Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHR_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3735) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let result : Int := ((_shr_int_general w__2 shift_amount) : Int)
                let w__3 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e esize
                    (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__4)
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, 0 ≤
  m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHRN_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3738)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let result := ((w__1 >>> shift_amount) : (BitVec (2 * esize)))
          let w__2 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
                (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 64) )
          (D_set d w__3)
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec (2 * esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount :
  Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSLI_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let shifted_op ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3741)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let mask : (BitVec esize) := (Sail.BitVec.castWidth ((Ones (n := esize)) <<< shift_amount))
  let shifted_op ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := shifted_op
      for r in [loop_r_lower:loop_r_upper:1]i do
        let shifted_op := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := shifted_op
            for e in [loop_e_lower:loop_e_upper:1]i do
              let shifted_op := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let shifted_op := ((w__1 <<< shift_amount) : (BitVec esize))
                let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
                    (Sail.BitVec.castWidth ((w__4 &&& (Complement.complement mask)) ||| shifted_op))))
                  ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure (shifted_op))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec esize) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, shift_amount : Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSRA_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3748) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let result : Int := ((_shr_int_general w__2 shift_amount) : Int)
                let w__3 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
                  (BitVec esize) )
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e esize
                    (Sail.BitVec.castWidth (BitVec.addInt w__5 result)))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__6)
                (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount :
  Int, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSRI_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let shifted_op ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3751)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let mask : (BitVec esize) := (Sail.BitVec.castWidth ((Ones (n := esize)) >>> shift_amount))
  let shifted_op ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := shifted_op
      for r in [loop_r_lower:loop_r_upper:1]i do
        let shifted_op := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := shifted_op
            for e in [loop_e_lower:loop_e_upper:1]i do
              let shifted_op := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let shifted_op := ((w__1 >>> shift_amount) : (BitVec esize))
                let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
                    (Sail.BitVec.castWidth ((w__4 &&& (Complement.complement mask)) ||| shifted_op))))
                  ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure (shifted_op))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec esize) )
  (pure (()))


end ArmFull.Functions
