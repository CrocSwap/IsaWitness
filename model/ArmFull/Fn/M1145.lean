module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0957
public import ArmFull.Fn.M0958
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1126
public import ArmFull.Fn.M1127 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VNMLA_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (vtype : VFPNegMul) : SailM Unit := do
  let product16 ← (( do (undefined_bitvector_at (← occLabel 3559) 16) ) : SailM (BitVec 16) )
  let product32 ← (( do (undefined_bitvector_at (← occLabel 3560) 32) ) : SailM (BitVec 32) )
  let product64 ← (( do (undefined_bitvector_at (← occLabel 3561) 64) ) : SailM (BitVec 64) )
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
      let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__2 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let product16 ← (( do
        (FPMul (Sail.BitVec.extractLsb w__0 15 0) (Sail.BitVec.extractLsb w__1 15 0) w__2) ) : SailM
        (BitVec 16) )
      match vtype with
      | .VFPNegMul_VNMLA =>
        (do
          let w__3 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__4 ← (( do (FPNeg (Sail.BitVec.extractLsb w__3 15 0)) ) : SailM (BitVec 16) )
          let w__5 ← (( do (FPNeg product16) ) : SailM (BitVec 16) )
          let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__7 ← (( do (FPAdd w__4 w__5 w__6) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__7)))
      | .VFPNegMul_VNMLS =>
        (do
          let w__8 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__9 ← (( do (FPNeg (Sail.BitVec.extractLsb w__8 15 0)) ) : SailM (BitVec 16) )
          let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__11 ← (( do (FPAdd w__9 product16 w__10) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__11)))
      | .VFPNegMul_VNMUL =>
        (do
          let w__12 ← (( do (FPNeg product16) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__12))))
  | 32 =>
    (do
      let w__13 ← (( do (S_read n) ) : SailM (BitVec 32) )
      let w__14 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__15 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let product32 ← (( do (FPMul w__13 w__14 w__15) ) : SailM (BitVec 32) )
      match vtype with
      | .VFPNegMul_VNMLA =>
        (do
          let w__16 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__17 ← (( do (FPNeg w__16) ) : SailM (BitVec 32) )
          let w__18 ← (( do (FPNeg product32) ) : SailM (BitVec 32) )
          let w__19 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__20 ← (( do (FPAdd w__17 w__18 w__19) ) : SailM (BitVec 32) )
          (S_set d w__20))
      | .VFPNegMul_VNMLS =>
        (do
          let w__21 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__22 ← (( do (FPNeg w__21) ) : SailM (BitVec 32) )
          let w__23 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__24 ← (( do (FPAdd w__22 product32 w__23) ) : SailM (BitVec 32) )
          (S_set d w__24))
      | .VFPNegMul_VNMUL =>
        (do
          let w__25 ← (( do (FPNeg product32) ) : SailM (BitVec 32) )
          (S_set d w__25)))
  | 64 =>
    (do
      let w__26 ← (( do (D_read n) ) : SailM (BitVec 64) )
      let w__27 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__28 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let product64 ← (( do (FPMul w__26 w__27 w__28) ) : SailM (BitVec 64) )
      match vtype with
      | .VFPNegMul_VNMLA =>
        (do
          let w__29 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__30 ← (( do (FPNeg w__29) ) : SailM (BitVec 64) )
          let w__31 ← (( do (FPNeg product64) ) : SailM (BitVec 64) )
          let w__32 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__33 ← (( do (FPAdd w__30 w__31 w__32) ) : SailM (BitVec 64) )
          (D_set d w__33))
      | .VFPNegMul_VNMLS =>
        (do
          let w__34 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__35 ← (( do (FPNeg w__34) ) : SailM (BitVec 64) )
          let w__36 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__37 ← (( do (FPAdd w__35 product64 w__36) ) : SailM (BitVec 64) )
          (D_set d w__37))
      | .VFPNegMul_VNMUL =>
        (do
          let w__38 ← (( do (FPNeg product64) ) : SailM (BitVec 64) )
          (D_set d w__38)))
  | _ => (pure (()))


/-- Type quantifiers: d : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPADD_f_Op_A_txt (d : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector_at (← occLabel 3577) 64) ) : SailM (BitVec 64) )
  let h : Nat := (Sail.Int.toNatChecked ((Int.ediv elements 2)))
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
          let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
          let w__5 ← (( do (FPAdd w__1 w__3 w__4) ) : SailM (BitVec esize) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest e esize (Sail.BitVec.castWidth w__5))) ) :
            SailM (BitVec 64) )
          let dest := (w__6 : (BitVec 64))
          let w__7 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let w__9 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__9 ((2 *i e) +i 1) esize))
            ) : SailM (BitVec esize) )
          let w__11 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
          let w__12 ← (( do (FPAdd w__8 w__10 w__11) ) : SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set dest (e +i h) esize (Sail.BitVec.castWidth w__12)))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (D_set d dest)


/-- Type quantifiers: d : Nat, elements : Nat, esize : Nat, m : Nat, k_maximum : Bool, n : Nat, 0
  ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPMAX_f_Op_A_txt (d : Nat) (elements : Nat) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) : SailM Unit := do
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3582)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3583)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector_at (← occLabel 3584) 64) ) : SailM (BitVec 64) )
  let h : Nat := (Sail.Int.toNatChecked ((Int.ediv elements 2)))
  let (dest, op1, op2) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (h -i 1)
    (do
      let mut loop_vars := (dest, op1, op2)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dest, op1, op2) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let op1 := (w__1 : (BitVec esize))
          let w__2 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 ((2 *i e) +i 1) esize)) )
            : SailM (BitVec esize) )
          let op2 := (w__3 : (BitVec esize))
          let w__8 ← (( do
            if (maximum : Bool)
            then
              (do
                let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                (FPMax op1 op2 w__4))
            else
              (do
                let w__6 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                (FPMin op1 op2 w__6)) ) : SailM (BitVec esize) )
          let w__9 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest e esize (Sail.BitVec.castWidth w__8))) ) :
            SailM (BitVec 64) )
          let dest := (w__9 : (BitVec 64))
          let w__10 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__11 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__10 (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let op1 := (w__11 : (BitVec esize))
          let w__12 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__13 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__12 ((2 *i e) +i 1) esize))
            ) : SailM (BitVec esize) )
          let op2 := (w__13 : (BitVec esize))
          let w__18 ← (( do
            if (maximum : Bool)
            then
              (do
                let w__14 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                (FPMax op1 op2 w__14))
            else
              (do
                let w__16 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                (FPMin op1 op2 w__16)) ) : SailM (BitVec esize) )
          let w__19 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set dest (e +i h) esize
              (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec 64) )
          let dest := (w__19 : (BitVec 64))
          (pure ((dest, op1, op2)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (D_set d dest)


def decode_aarch32_instrs_VRECPE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        (pure ((← do
              if (((size == 0b01#2) : Bool) : Bool)
              then
                (do
                  (pure ((← do
                        let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                        (pure (((! w__1) : Bool)))) || ((F == 0#1) : Bool))))
              else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool
        )
      if (w__4 : Bool)
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
      (execute_aarch32_instrs_VRECPE_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRECPE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        (pure ((← do
              if (((size == 0b01#2) : Bool) : Bool)
              then
                (do
                  (pure ((← do
                        let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                        (pure (((! w__1) : Bool)))) || ((F == 0#1) : Bool))))
              else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool
        )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__6 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
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
      (execute_aarch32_instrs_VRECPE_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRSQRTE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        (pure ((← do
              if (((size == 0b01#2) : Bool) : Bool)
              then
                (do
                  (pure ((← do
                        let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                        (pure (((! w__1) : Bool)))) || ((F == 0#1) : Bool))))
              else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool
        )
      if (w__4 : Bool)
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
      let w__4 ← (( do
        (pure ((← do
              if (((size == 0b01#2) : Bool) : Bool)
              then
                (do
                  (pure ((← do
                        let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                        (pure (((! w__1) : Bool)))) || ((F == 0#1) : Bool))))
              else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool
        )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__6 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
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
  let w__2 ← (( do
    (pure ((← do
          if (((size == 0b01#2) : Bool) : Bool)
          then
            (do
              let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
              (pure (((! w__0) : Bool))))
          else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
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
  let w__3 ← (( do
    (pure ((← do
          if (((size == 0b01#2) : Bool) : Bool)
          then
            (do
              let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) || (((size == 0b00#2) || (size == 0b11#2)) : Bool))) ) : SailM Bool )
  if (w__3 : Bool)
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
  let w__2 ← (( do
    if (((size == 0b00#2) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__2 : Bool)
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


end ArmFull.Functions
