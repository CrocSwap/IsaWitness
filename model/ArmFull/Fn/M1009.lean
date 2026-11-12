import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0063
import ArmFull.Fn.M0115
import ArmFull.Fn.M0124
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
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

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m
  : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VHADD_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3444) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 3445) ()) ) : SailM Int )
  let result ← (( do (undefined_int_at (← occLabel 3446) ()) ) : SailM Int )
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
                let result : Int :=
                  if (add : Bool)
                  then (Int.shiftr (op1 +i op2) 1)
                  else (Int.shiftr (op1 -i op2) 1)
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


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_maximum
  : Bool, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAX_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3458) ()) ) : SailM Int )
  let op2 ← (( do (undefined_int_at (← occLabel 3459) ()) ) : SailM Int )
  let result ← (( do (undefined_int_at (← occLabel 3460) ()) ) : SailM Int )
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
                let result : Int :=
                  if (maximum : Bool)
                  then (Max.max op1 op2)
                  else (Min.min op1 op2)
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


/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination
  : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_i_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do (undefined_int_at (← occLabel 3478) ()) ) : SailM Int )
  let product ← (( do (undefined_int_at (← occLabel 3479) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (addend, product) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (addend, product)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (addend, product) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (addend, product)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (addend, product) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
                let product : Int := ((w__2 *i w__5) : Int)
                let addend : Int :=
                  if (add : Bool)
                  then product
                  else (Neg.neg product)
                if (long_destination : Bool)
                then
                  (do
                    let w__6 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__7 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__8 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e
                        (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                    let w__9 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                        (Sail.Int.toNatChecked ((2 *i esize)))
                        (Sail.BitVec.castWidth (BitVec.addInt w__8 addend)))) ) : SailM (BitVec 128)
                      )
                    (Q_set (Int.shiftr d 1) w__9))
                else
                  (do
                    let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__11 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__11 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__13 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                        (Sail.BitVec.castWidth (BitVec.addInt w__12 addend)))) ) : SailM (BitVec 64)
                      )
                    (D_set (d +i r) w__13))
                (pure ((addend, product)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int) )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOVX_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
  (S_set d ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb w__0 31 16)))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VINS_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do (S_read d) ) : SailM (BitVec 32) )
  (S_set d ((Sail.BitVec.extractLsb w__0 15 0) +++ (Sail.BitVec.extractLsb w__1 15 0)))


/-- Type quantifiers: m : Nat, t : Nat, t2 : Nat, k_to_arm_registers : Bool, 0 ≤ t2 ∧
  t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch32_instrs_VMOV_d_Op_A_txt (m : Nat) (t : Nat) (t2 : Nat) (to_arm_registers : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_registers : Bool)
  then
    (do
      let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
      (R_set t (Sail.BitVec.extractLsb w__0 31 0))
      let w__1 ← (( do (D_read m) ) : SailM (BitVec 64) )
      (R_set t2 (Sail.BitVec.extractLsb w__1 63 32)))
  else
    (do
      let w__2 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (D_set m (Sail.BitVec.updateSubrange w__2 31 0 w__3))
      let w__4 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__5 ← (( do (R_read t2) ) : SailM (BitVec 32) )
      (D_set m (Sail.BitVec.updateSubrange w__4 63 32 w__5)))


/-- Type quantifiers: k_advsimd : Bool, d : Nat, regs : Nat, k_single_register : Bool, List.elem
  regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOV_i_Op_A_txt (advsimd : Bool) (d : Nat) (imm32 : (BitVec 32)) (imm64 : (BitVec 64)) (regs : Nat) (single_register : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (single_register : Bool)
  then
    (do
      (S_set d imm32))
  else
    (do
      let loop_r_lower : Nat := 0
      let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
      (do
        let mut loop_vars := ()
        for r in [loop_r_lower:loop_r_upper:1]i do
          let () := loop_vars
          loop_vars ← do (D_set (d +i r) imm64)
        (pure loop_vars)))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, 0
  ≤ m ∧
  m ≤ 31 ∧ List.elem esize [0, 8, 16, 24, 32, 40, 48, 56] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOVL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3508) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          ArmFull.assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i esize) ≤b 64)))) "sail-arm/instrs32.sail:28727.131-28727.132"
          let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
            (BitVec esize) )
          let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let result : Int := (w__2 : Int)
          let w__3 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange result ((2 *i esize) -i 1) 0)))) ) : SailM
            (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__4)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOVN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read d) ) : SailM (BitVec 64) )
        let w__1 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
        let w__2 ← (( do
          ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e (Sail.Int.toNatChecked ((2 *i esize))))) )
          : SailM (BitVec (2 * esize)) )
        let w__3 ← (( do
          ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2
              (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 64) )
        (D_set d w__3)
    (pure loop_vars))


/-- Type quantifiers: n : Nat, t : Nat, k_to_arm_register : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch32_instrs_VMOV_h_Op_A_txt (n : Nat) (t : Nat) (to_arm_register : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_register : Bool)
  then
    (do
      let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
      (R_set t ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb w__0 15 0))))
  else
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (S_set n ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb w__1 15 0))))


/-- Type quantifiers: k_advsimd : Bool, d : Nat, m : Nat, regs : Nat, k_single_register : Bool, regs
  = 1 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOV_r_Op_A_txt (advsimd : Bool) (d : Nat) (m : Nat) (regs : Nat) (single_register : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (single_register : Bool)
  then
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      (S_set d w__0))
  else
    (do
      let loop_r_lower : Nat := 0
      let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
      (do
        let mut loop_vars := ()
        for r in [loop_r_lower:loop_r_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            (D_set (d +i r) w__1)
        (pure loop_vars)))


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, esize : Nat, index : Int, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOV_rs_Op_A_txt (advsimd : Bool) (d__arg : Nat) (esize : Nat) (index : Int) (t : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  let w__0 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 index esize
      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1 (Sail.Int.toNatChecked ((esize -i 1))) 0))))
    ) : SailM (BitVec 64) )
  (D_set d w__2)


/-- Type quantifiers: n : Nat, t : Nat, k_to_arm_register : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch32_instrs_VMOV_s_Op_A_txt (n : Nat) (t : Nat) (to_arm_register : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_register : Bool)
  then
    (do
      let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
      (R_set t w__0))
  else
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (S_set n w__1))


/-- Type quantifiers: k_advsimd : Bool, esize : Nat, index : Int, k_is_unsigned : Bool, n : Nat, t :
  Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] -/
def execute_aarch32_instrs_VMOV_sr_Op_A_txt (advsimd : Bool) (esize : Nat) (index : Int) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (is_unsigned : Bool)
  then
    (do
      let w__0 ← (( do (D_read n) ) : SailM (BitVec 64) )
      let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
        (BitVec esize) )
      (R_set t (Sail.BitVec.zeroExtend w__1 32)))
  else
    (do
      let w__2 ← (( do (D_read n) ) : SailM (BitVec 64) )
      let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 index esize)) ) : SailM
        (BitVec esize) )
      (R_set t (sign_extend w__3 32)))


/-- Type quantifiers: m : Nat, t : Nat, t2 : Nat, k_to_arm_registers : Bool, 0 ≤ t2 ∧
  t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch32_instrs_VMOV_ss_Op_A_txt (m : Nat) (t : Nat) (t2 : Nat) (to_arm_registers : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_registers : Bool)
  then
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      (R_set t w__0)
      let w__1 ← (( do (S_read (m +i 1)) ) : SailM (BitVec 32) )
      (R_set t2 w__1))
  else
    (do
      let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (S_set m w__2)
      let w__3 ← (( do (R_read t2) ) : SailM (BitVec 32) )
      (S_set (m +i 1) w__3))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination
  : Bool, m : Nat, n : Nat, k_polynomial : Bool, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (polynomial : Bool) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3533)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int_at (← occLabel 3534) ()) ) : SailM Int )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3535)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2val ← (( do (undefined_int_at (← occLabel 3536) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op1val, op2, op2val) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op1val, op2, op2val)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op1val, op2, op2val) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op1val, op2, op2val)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op1val, op2, op2val) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let op1val : Int := (w__2 : Int)
                let w__3 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__4 : (BitVec esize))
                let w__5 ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
                let op2val : Int := (w__5 : Int)
                let product ← (( do
                  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3537)
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let product : (BitVec (2 * esize)) :=
                  if (polynomial : Bool)
                  then (Sail.BitVec.castWidth (PolynomialMult op1 op2))
                  else
                    (Sail.BitVec.castWidth (integer_subrange (op1val *i op2val) ((2 *i esize) -i 1)
                      0))
                if (long_destination : Bool)
                then
                  (do
                    let w__6 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__7 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                        (Sail.Int.toNatChecked ((2 *i esize))) (Sail.BitVec.castWidth product))) ) :
                      SailM (BitVec 128) )
                    (Q_set (Int.shiftr d 1) w__7))
                else
                  (do
                    let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__9 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb product
                          (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__9))
                (pure ((op1, op1val, op2, op2val)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × Int × (BitVec esize) × Int) )
  (pure (()))


/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMVN_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do (D_set (d +i r) (Complement.complement imm64))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMVN_r_Op_A_txt (d : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (Complement.complement w__0))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORN_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 ||| (Complement.complement w__1)))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORR_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 ||| imm64))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 ||| w__1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VPADAL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3574)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3575)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_int_at (← occLabel 3576) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let h : Int := (fdiv_int elements 2)
  let (op1, op2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (h -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 (2 *i e) esize)) )
                  : SailM (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 ((2 *i e) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let w__4 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let w__5 ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
                let result : Int := ((w__4 +i w__5) : Int)
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let w__9 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                    (Sail.Int.toNatChecked ((2 *i esize)))
                    (Sail.BitVec.castWidth (BitVec.addInt w__8 result)))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__9)
                (pure ((op1, op2, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
  (pure (()))


/-- Type quantifiers: d : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPADD_i_Op_A_txt (d : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector_at (← occLabel 3578) 64) ) : SailM (BitVec 64) )
  let h : Int := (fdiv_int elements 2)
  let dest ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (h -i 1)
    (do
      let mut loop_vars := dest
      for e in [loop_e_lower:loop_e_upper:1]i do
        let dest := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__2 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 ((2 *i e) +i 1) esize)) )
            : SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest e esize
              (Sail.BitVec.castWidth (w__1 + w__3)))) ) : SailM (BitVec 64) )
          let dest := (w__4 : (BitVec 64))
          let w__5 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__7 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 ((2 *i e) +i 1) esize)) )
            : SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set dest (e +i h) esize
            (Sail.BitVec.castWidth (w__6 + w__8))))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (D_set d dest)


end ArmFull.Functions
