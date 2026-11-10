import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0099
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1075

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

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs
  : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
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
                  let w__6 ← (( do (FPMul w__2 w__4 w__5) ) : SailM (BitVec esize) )
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
            (FPMul (Sail.BitVec.extractLsb w__8 15 0) (Sail.BitVec.extractLsb w__9 15 0) w__10) ) :
            SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__11)))
      | 32 =>
        (do
          let w__12 ← (( do (S_read n) ) : SailM (BitVec 32) )
          let w__13 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__14 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__15 ← (( do (FPMul w__12 w__13 w__14) ) : SailM (BitVec 32) )
          (S_set d w__15))
      | 64 =>
        (do
          let w__16 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__17 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__18 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__19 ← (( do (FPMul w__16 w__17 w__18) ) : SailM (BitVec 64) )
          (D_set d w__19))
      | _ => (pure (())))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, index :
  Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3] ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_s_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (index : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3538)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int_at (← occLabel 3539) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let op2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
    (BitVec esize) )
  let op2val ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
  let (op1, op1val) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op1val)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op1val) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, op1val)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op1val) := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__2 : (BitVec esize))
                let w__3 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let op1val : Int := (w__3 : Int)
                if (floating_point : Bool)
                then
                  (do
                    let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__6 ← (( do (FPMul op1 op2 w__5) ) : SailM (BitVec esize) )
                    let w__7 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                        (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__7))
                else
                  (do
                    if (long_destination : Bool)
                    then
                      (do
                        let w__8 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                        let w__9 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e
                            (Sail.Int.toNatChecked ((2 *i esize)))
                            (Sail.BitVec.castWidth (integer_subrange (op1val *i op2val)
                              ((2 *i esize) -i 1) 0)))) ) : SailM (BitVec 128) )
                        (Q_set (Int.shiftr d 1) w__9))
                    else
                      (do
                        let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__11 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                            (Sail.BitVec.castWidth (integer_subrange (op1val *i op2val) (esize -i 1)
                              0)))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__11)))
                (pure ((op1, op1val)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × Int) )
  (pure (()))


def decode_aarch32_instrs_VNEG_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:30572.29-30572.30"
      let floating_point ← (( do (undefined_bool_at (← occLabel 3549) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3550) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3551) ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3552) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3553) 0 31))) ) :
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if ((((F == 1#1) && (size == 0b01#2)) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool_at (← occLabel 3554) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3555) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3556) ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
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
      let w__5 ← (( do
        if ((← do
             let w__3 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__3) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__4 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__4) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3557) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3558) 0 31))) ) :
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


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
      (execute_aarch32_instrs_VRECPE_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize)) floating_point
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


end ArmFull.Functions
