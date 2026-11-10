import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1071
import ArmFull.Fn.M1075
import ArmFull.Fn.M1076

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

def decode_aarch32_instrs_VRSQRTE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let floating_point : Bool := (F == 1#1)
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
        | 0b10 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ => (elements, esize)
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSQRTE_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRSQRTE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let floating_point : Bool := (F == 1#1)
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
        | 0b10 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ => (elements, esize)
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSQRTE_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSQRT_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (FPSqrt (Sail.BitVec.extractLsb w__0 15 0) w__1) ) : SailM (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__2)))
  | 32 =>
    (do
      let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__5 ← (( do (FPSqrt w__3 w__4) ) : SailM (BitVec 32) )
      (S_set d w__5))
  | 64 =>
    (do
      let w__6 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__8 ← (( do (FPSqrt w__6 w__7) ) : SailM (BitVec 64) )
      (D_set d w__8))
  | _ => (pure (()))


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs
  : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUB_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower : Nat := 0
      let loop_r_upper : Int := (regs -i 1)
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
                  let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__6 ← (( do (FPSub w__2 w__4 w__5) ) : SailM (BitVec esize) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                      (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__7)
              (pure loop_vars_1))
        (pure loop_vars)))
  else
    (do
      match esize with
      | 16 =>
        (do
          let w__8 ← (( do (S_read n) ) : SailM (BitVec 32) )
          let w__9 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__11 ← (( do
            (FPSub (Sail.BitVec.extractLsb w__8 15 0) (Sail.BitVec.extractLsb w__9 15 0) w__10) ) :
            SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__11)))
      | 32 =>
        (do
          let w__12 ← (( do (S_read n) ) : SailM (BitVec 32) )
          let w__13 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__14 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__15 ← (( do (FPSub w__12 w__13 w__14) ) : SailM (BitVec 32) )
          (S_set d w__15))
      | 64 =>
        (do
          let w__16 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__17 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__18 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__19 ← (( do (FPSub w__16 w__17 w__18) ) : SailM (BitVec 64) )
          (D_set d w__19))
      | _ => (pure (())))


def decode_aarch32_instrs_VCVTA_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (RM : (BitVec 2)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 1#1)
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VCVTA_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (regs)) rounding is_unsigned)


def decode_aarch32_instrs_VCVTA_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (RM : (BitVec 2)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 1#1)
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VCVTA_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (regs)) rounding is_unsigned)


def decode_aarch32_instrs_VCVTA_vfp_A1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 0#1)
  let d : Int := (BitVec.toNat (Vd +++ D))
  let esize : Int := 16
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3805) 0 31))) ) :
    SailM Nat )
  let (esize, m) : (Int × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (esize, m))
    | 0b10 =>
      (let esize : Int := 32
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (esize, m))
    | 0b11 =>
      (let esize : Int := 64
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (esize, m))
    | _ => (esize, m)
  let m : Int := m
  let esize : Int := esize
  (execute_aarch32_instrs_VCVTA_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) rounding is_unsigned)


def decode_aarch32_instrs_VCVTA_vfp_T1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 0#1)
  let d : Int := (BitVec.toNat (Vd +++ D))
  let esize : Int := 16
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3806) 0 31))) ) :
    SailM Nat )
  let (esize, m) : (Int × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (esize, m))
    | 0b10 =>
      (let esize : Int := 32
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (esize, m))
    | 0b11 =>
      (let esize : Int := 64
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (esize, m))
    | _ => (esize, m)
  let m : Int := m
  let esize : Int := esize
  (execute_aarch32_instrs_VCVTA_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) rounding is_unsigned)


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, k_maximum
  : Bool, n : Nat, regs : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAXNM_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3807)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3808)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let (op1, op2) ← (( do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Int := (regs -i 1)
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
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let op1 := (w__1 : (BitVec esize))
                    let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) :
                      SailM (BitVec esize) )
                    let op2 := (w__3 : (BitVec esize))
                    if (maximum : Bool)
                    then
                      (do
                        let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                        let w__6 ← (( do (FPMaxNum op1 op2 w__5) ) : SailM (BitVec esize) )
                        let w__7 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                            (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__7))
                    else
                      (do
                        let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__9 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                        let w__10 ← (( do (FPMinNum op1 op2 w__9) ) : SailM (BitVec esize) )
                        let w__11 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                            (Sail.BitVec.castWidth w__10))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__11))
                    (pure ((op1, op2)))
                (pure loop_vars_1))
          (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
      (pure (())))
  else
    (do
      match esize with
      | 16 =>
        (do
          if (maximum : Bool)
          then
            (do
              let w__12 ← (( do (S_read n) ) : SailM (BitVec 32) )
              let w__13 ← (( do (S_read m) ) : SailM (BitVec 32) )
              let w__14 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__15 ← (( do
                (FPMaxNum (Sail.BitVec.extractLsb w__12 15 0) (Sail.BitVec.extractLsb w__13 15 0)
                  w__14) ) : SailM (BitVec 16) )
              (S_set d ((Zeros (n := 16)) +++ w__15)))
          else
            (do
              let w__16 ← (( do (S_read n) ) : SailM (BitVec 32) )
              let w__17 ← (( do (S_read m) ) : SailM (BitVec 32) )
              let w__18 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__19 ← (( do
                (FPMinNum (Sail.BitVec.extractLsb w__16 15 0) (Sail.BitVec.extractLsb w__17 15 0)
                  w__18) ) : SailM (BitVec 16) )
              (S_set d ((Zeros (n := 16)) +++ w__19))))
      | 32 =>
        (do
          if (maximum : Bool)
          then
            (do
              let w__20 ← (( do (S_read n) ) : SailM (BitVec 32) )
              let w__21 ← (( do (S_read m) ) : SailM (BitVec 32) )
              let w__22 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__23 ← (( do (FPMaxNum w__20 w__21 w__22) ) : SailM (BitVec 32) )
              (S_set d w__23))
          else
            (do
              let w__24 ← (( do (S_read n) ) : SailM (BitVec 32) )
              let w__25 ← (( do (S_read m) ) : SailM (BitVec 32) )
              let w__26 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__27 ← (( do (FPMinNum w__24 w__25 w__26) ) : SailM (BitVec 32) )
              (S_set d w__27)))
      | 64 =>
        (do
          if (maximum : Bool)
          then
            (do
              let w__28 ← (( do (D_read n) ) : SailM (BitVec 64) )
              let w__29 ← (( do (D_read m) ) : SailM (BitVec 64) )
              let w__30 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__31 ← (( do (FPMaxNum w__28 w__29 w__30) ) : SailM (BitVec 64) )
              (D_set d w__31))
          else
            (do
              let w__32 ← (( do (D_read n) ) : SailM (BitVec 64) )
              let w__33 ← (( do (D_read m) ) : SailM (BitVec 64) )
              let w__34 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
              let w__35 ← (( do (FPMinNum w__32 w__33 w__34) ) : SailM (BitVec 64) )
              (D_set d w__35)))
      | _ => (pure (())))


def decode_aarch32_instrs_VRINTA_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 3)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 2)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
           op 0)]))) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do
    (FPDecodeRM
      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 2)])) +++ (Complement.complement
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)]))))) ) : SailM FPRounding )
  let exact : Bool := false
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VRINTA_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTA_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 3)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 2)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
           op 0)]))) : Bool)
  then sailThrow ((Error_See "Related encodings"))
  else (pure (()))
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do
    (FPDecodeRM
      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 2)])) +++ (Complement.complement
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)]))))) ) : SailM FPRounding )
  let exact : Bool := false
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
    | 0b10 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ => (elements, esize)
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VRINTA_asimd_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) rounding)


def decode_aarch32_instrs_VRINTA_vfp_A1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let exact : Bool := false
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3821) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3822) 0 31))) ) :
    SailM Nat )
  let (d, esize, m) : (Nat × Int × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m))
    | _ => (d, esize, m)
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VRINTA_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m)) rounding)


def decode_aarch32_instrs_VRINTA_vfp_T1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let exact : Bool := false
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3823) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3824) 0 31))) ) :
    SailM Nat )
  let (d, esize, m) : (Nat × Int × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m))
    | _ => (d, esize, m)
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VRINTA_vfp_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (m)) rounding)


end ArmFull.Functions
