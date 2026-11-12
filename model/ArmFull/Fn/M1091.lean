import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0018
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0150
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1071
import ArmFull.Fn.M1074
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

def decode_aarch32_instrs_VCMP_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:22361.29-22361.30"
      let m ← (( do (undefined_int_at (← occLabel 3386) ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let m : Int := m
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := true
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3387) 0 31))) ) :
        SailM Nat )
      let (d, esize) : (Nat × Int) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, esize))
        | _ => (d, esize)
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VCMP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) m quiet_nan_exc with_zero))
  else (pure (()))


def decode_aarch32_instrs_VCMP_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
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
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3388) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3389) 0 31))) ) :
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
      (execute_aarch32_instrs_VCMP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) m quiet_nan_exc with_zero))
  else (pure (()))


def decode_aarch32_instrs_VCMP_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3390) ()) ) : SailM Int )
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
      let m : Int := m
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := true
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3391) 0 31))) ) :
        SailM Nat )
      let (d, esize) : (Nat × Int) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, esize))
        | _ => (d, esize)
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VCMP_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) m quiet_nan_exc with_zero))
  else (pure (()))


/-- Type quantifiers: k_convert_from_half : Bool, d : Nat, lowbit : Nat, m : Nat, k_uses_double :
  Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem lowbit [0, 16] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTB_Op_A_txt (convert_from_half : Bool) (d : Nat) (lowbit : Nat) (m : Nat) (uses_double : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  let hp ← (( do (undefined_bitvector_at (← occLabel 3392) 16) ) : SailM (BitVec 16) )
  if (convert_from_half : Bool)
  then
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let hp : (BitVec 16) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((lowbit +i 15)))
          lowbit))
      if (uses_double : Bool)
      then
        (do
          let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (FPConvert__1 hp w__1 64) ) : SailM (BitVec 64) )
          (D_set d w__2))
      else
        (do
          let w__3 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPConvert__1 hp w__3 32) ) : SailM (BitVec 32) )
          (S_set d w__4)))
  else
    (do
      let hp ← (( do
        if (uses_double : Bool)
        then
          (do
            let w__5 ← (( do (D_read m) ) : SailM (BitVec 64) )
            let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            (FPConvert__1 w__5 w__6 16))
        else
          (do
            let w__8 ← (( do (S_read m) ) : SailM (BitVec 32) )
            let w__9 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            (FPConvert__1 w__8 w__9 16)) ) : SailM (BitVec 16) )
      let w__11 ← (( do (S_read d) ) : SailM (BitVec 32) )
      (S_set d
        (Sail.BitVec.updateSubrange w__11 (Sail.Int.toNatChecked ((lowbit +i 15))) lowbit
          (Sail.BitVec.castWidth hp))))


/-- Type quantifiers: d : Nat, k_double_to_single : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_ds_Op_A_txt (d : Nat) (double_to_single : Bool) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  if (double_to_single : Bool)
  then
    (do
      let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (FPConvert__1 w__0 w__1 32) ) : SailM (BitVec 32) )
      (S_set d w__2))
  else
    (do
      let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__5 ← (( do (FPConvert__1 w__3 w__4 64) ) : SailM (BitVec 64) )
      (D_set d w__5))


/-- Type quantifiers: d__arg : Nat, elements : Nat, k_half_to_single : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_hs_Op_A_txt (d__arg : Nat) (elements : Nat) (half_to_single : Bool) (m : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_e_lower : Nat := 0
  let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if (half_to_single : Bool)
        then
          (do
            let w__0 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
            let w__1 ← (( do (Din_read m) ) : SailM (BitVec 64) )
            let w__2 ← (( do (Elem_read w__1 e 16) ) : SailM (BitVec 16) )
            let w__3 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPConvert__1 w__2 w__3 32) ) : SailM (BitVec 32) )
            let w__5 ← (( do (Elem_set w__0 e 32 w__4) ) : SailM (BitVec 128) )
            (Q_set (Int.shiftr d 1) w__5))
        else
          (do
            let w__6 ← (( do (D_read d) ) : SailM (BitVec 64) )
            let w__7 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
            let w__8 ← (( do (Elem_read w__7 e 32) ) : SailM (BitVec 32) )
            let w__9 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
            let w__10 ← (( do (FPConvert__1 w__8 w__9 16) ) : SailM (BitVec 16) )
            let w__11 ← (( do (Elem_set w__6 e 16 w__10) ) : SailM (BitVec 64) )
            (D_set d w__11))
    (pure loop_vars))


def decode_aarch32_instrs_VCVT_is_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let to_integer : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 1#1)
      let is_unsigned : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
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
      (execute_aarch32_instrs_VCVT_is_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) to_integer is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_is_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
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
      let to_integer : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 1#1)
      let is_unsigned : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
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
      (execute_aarch32_instrs_VCVT_is_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (regs)) to_integer is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_iv_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 3)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:22999.29-22999.30"
      if (((opc2 != 0b000#3) && (let b__0 := opc2
           (! (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b10#2 : (BitVec 2))) : Bool)
             then true
             else false : Bool)))) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3399) 0 31))) ) :
        SailM Nat )
      let esize : Int := 16
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3400) 0 31))) ) :
        SailM Nat )
      let is_unsigned ← (( do (undefined_bool_at (← occLabel 3401) ()) ) : SailM Bool )
      let rounding ← (( do (undefined_FPRounding (← occLabel 3402) ()) ) : SailM FPRounding )
      let to_integer : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 2)])) == 1#1)
      let (d, esize, is_unsigned, m, rounding) ← (( do
        if (to_integer : Bool)
        then
          (do
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
            let w__3 ← (( do
              if ((op == 1#1) : Bool)
              then (pure (FPRounding_ZERO))
              else
                (do
                  let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                  (FPRoundingMode w__1)) ) : SailM FPRounding )
            let rounding := (w__3 : FPRounding)
            let d : Nat := (BitVec.toNat (Vd +++ D))
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
            (pure ((d, esize, is_unsigned, m, rounding))))
        else
          (do
            let is_unsigned : Bool := (op == 0#1)
            let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            let w__5 ← (( do (FPRoundingMode w__4) ) : SailM FPRounding )
            let rounding := (w__5 : FPRounding)
            let m : Nat := (BitVec.toNat (Vm +++ M))
            let (d, esize) : (Nat × Int) :=
              match size with
              | 0b01 =>
                (let esize : Int := 16
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b10 =>
                (let esize : Int := 32
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b11 =>
                (let esize : Int := 64
                let d : Nat := (BitVec.toNat (D +++ Vd))
                (d, esize))
              | _ => (d, esize)
            (pure ((d, esize, is_unsigned, m, rounding)))) ) : SailM
        (Nat × Int × Bool × Nat × FPRounding) )
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VCVT_iv_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) rounding to_integer is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_iv_T1enc_A_txt (D : (BitVec 1)) (opc2 : (BitVec 3)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((opc2 != 0b000#3) && (let b__0 := opc2
           (! (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b10#2 : (BitVec 2))) : Bool)
             then true
             else false : Bool)))) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
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
      let esize : Int := 16
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3403) 0 31))) ) :
        SailM Nat )
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3404) 0 31))) ) :
        SailM Nat )
      let is_unsigned ← (( do (undefined_bool_at (← occLabel 3405) ()) ) : SailM Bool )
      let rounding ← (( do (undefined_FPRounding (← occLabel 3406) ()) ) : SailM FPRounding )
      let to_integer : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 2)])) == 1#1)
      let (d, esize, is_unsigned, m, rounding) ← (( do
        if (to_integer : Bool)
        then
          (do
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
            let w__5 ← (( do
              if ((op == 1#1) : Bool)
              then (pure (FPRounding_ZERO))
              else
                (do
                  let w__3 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                  (FPRoundingMode w__3)) ) : SailM FPRounding )
            let rounding := (w__5 : FPRounding)
            let d : Nat := (BitVec.toNat (Vd +++ D))
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
            (pure ((d, esize, is_unsigned, m, rounding))))
        else
          (do
            let is_unsigned : Bool := (op == 0#1)
            let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            let w__7 ← (( do (FPRoundingMode w__6) ) : SailM FPRounding )
            let rounding := (w__7 : FPRounding)
            let m : Nat := (BitVec.toNat (Vm +++ M))
            let (d, esize) : (Nat × Int) :=
              match size with
              | 0b01 =>
                (let esize : Int := 16
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b10 =>
                (let esize : Int := 32
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b11 =>
                (let esize : Int := 64
                let d : Nat := (BitVec.toNat (D +++ Vd))
                (d, esize))
              | _ => (d, esize)
            (pure ((d, esize, is_unsigned, m, rounding)))) ) : SailM
        (Nat × Int × Bool × Nat × FPRounding) )
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VCVT_iv_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) rounding to_integer is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_xs_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := imm6
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) && (let b__1 := imm6
           (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 5 4)) == (0b10#2 : (BitVec 2))) : Bool)
           then true
           else false : Bool))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((let b__2 := imm6
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 5 5)) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let to_fixed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
      let frac_bits : Int := (64 -i (BitVec.toNat imm6))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) with
        | 0 =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
        | _ =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_xs_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (frac_bits)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs)) to_fixed is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_xs_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((let b__0 := imm6
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) && (let b__1 := imm6
           (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 5 4)) == (0b10#2 : (BitVec 2))) : Bool)
           then true
           else false : Bool))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((let b__2 := imm6
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 5 5)) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let to_fixed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 1#1)
      let frac_bits : Int := (64 -i (BitVec.toNat imm6))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) with
        | 0 =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
        | _ =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_xs_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (frac_bits)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (regs)) to_fixed is_unsigned))
  else (pure (()))


end ArmFull.Functions
