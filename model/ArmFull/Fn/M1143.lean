module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0957
public import ArmFull.Fn.M0958
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1126 set_option backward.proofsInPublic true @[expose] public section

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
      let w__3 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__5 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
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
            let w__8 ← (( do
              if ((op == 1#1) : Bool)
              then (pure (FPRounding_ZERO))
              else
                (do
                  let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                  (FPRoundingMode w__6)) ) : SailM FPRounding )
            let rounding := (w__8 : FPRounding)
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
            let w__9 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
            let w__10 ← (( do (FPRoundingMode w__9) ) : SailM FPRounding )
            let rounding := (w__10 : FPRounding)
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
      let w__2 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
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
      let w__2 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
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


def decode_aarch32_instrs_VCVT_xv_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (op : (BitVec 1)) (U : (BitVec 1)) (Vd : (BitVec 4)) (sf : (BitVec 2)) (sx : (BitVec 1)) (i : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:23359.29-23359.30"
      let w__3 ← (( do
        if (((sf == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((sf == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sf == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let to_fixed : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      let size : Int :=
        if ((sx == 0#1) : Bool)
        then 16
        else 32
      let frac_bits : Int := (size -i (BitVec.toNat (imm4 +++ i)))
      let fp_size : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3410) 0 31))) ) :
        SailM Nat )
      let (d, fp_size) : (Nat × Int) :=
        match sf with
        | 0b01 =>
          (let fp_size : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b10 =>
          (let fp_size : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b11 =>
          (let fp_size : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, fp_size))
        | _ => (d, fp_size)
      let fp_size : Int := fp_size
      let d : Int := d
      if ((frac_bits <b 0) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VCVT_xv_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (fp_size)) frac_bits (Sail.Int.toNatChecked (size)) to_fixed
        is_unsigned))
  else (pure (()))


def decode_aarch32_instrs_VCVT_xv_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (U : (BitVec 1)) (Vd : (BitVec 4)) (sf : (BitVec 2)) (sx : (BitVec 1)) (i : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__3 ← (( do
        if (((sf == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((sf == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__5 ← (( do
        if (((sf == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let to_fixed : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      let size : Int :=
        if ((sx == 0#1) : Bool)
        then 16
        else 32
      let frac_bits : Int := (size -i (BitVec.toNat (imm4 +++ i)))
      let fp_size : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3411) 0 31))) ) :
        SailM Nat )
      let (d, fp_size) : (Nat × Int) :=
        match sf with
        | 0b01 =>
          (let fp_size : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b10 =>
          (let fp_size : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b11 =>
          (let fp_size : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, fp_size))
        | _ => (d, fp_size)
      let fp_size : Int := fp_size
      let d : Int := d
      if ((frac_bits <b 0) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let d : Int := d
      (execute_aarch32_instrs_VCVT_xv_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (fp_size)) frac_bits (Sail.Int.toNatChecked (size)) to_fixed
        is_unsigned))
  else (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDIV_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
      let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__2 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__3 ← (( do
        (FPDiv (Sail.BitVec.extractLsb w__0 15 0) (Sail.BitVec.extractLsb w__1 15 0) w__2) ) : SailM
        (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__3)))
  | 32 =>
    (do
      let w__4 ← (( do (S_read n) ) : SailM (BitVec 32) )
      let w__5 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPDiv w__4 w__5 w__6) ) : SailM (BitVec 32) )
      (S_set d w__7))
  | 64 =>
    (do
      let w__8 ← (( do (D_read n) ) : SailM (BitVec 64) )
      let w__9 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__11 ← (( do (FPDiv w__8 w__9 w__10) ) : SailM (BitVec 64) )
      (D_set d w__11))
  | _ => (pure (()))


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_op1_neg
  : Bool, regs : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VFMA_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let op16 ← (( do (undefined_bitvector_at (← occLabel 3420) 16) ) : SailM (BitVec 16) )
  let op32 ← (( do (undefined_bitvector_at (← occLabel 3421) 32) ) : SailM (BitVec 32) )
  let op64 ← (( do (undefined_bitvector_at (← occLabel 3422) 64) ) : SailM (BitVec 64) )
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
                  let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                  let op1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                    SailM (BitVec esize) )
                  let op1 ← (( do
                    if (op1_neg : Bool)
                    then
                      (do
                        (FPNeg op1))
                    else (pure (op1)) ) : SailM (BitVec esize) )
                  let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__7 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (FPMulAdd w__4 op1 w__6 w__7) ) : SailM (BitVec esize) )
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__2 e esize
                      (Sail.BitVec.castWidth w__8))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__9)
              (pure loop_vars_1))
        (pure loop_vars)))
  else
    (do
      match esize with
      | 16 =>
        (do
          let op16 ← (( do
            if (op1_neg : Bool)
            then
              (do
                let w__10 ← (( do (S_read n) ) : SailM (BitVec 32) )
                (FPNeg (Sail.BitVec.extractLsb w__10 15 0)))
            else
              (do
                let w__12 ← (( do (S_read n) ) : SailM (BitVec 32) )
                (pure ((Sail.BitVec.extractLsb w__12 15 0)))) ) : SailM (BitVec 16) )
          let w__13 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__14 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__15 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__16 ← (( do
            (FPMulAdd (Sail.BitVec.extractLsb w__13 15 0) op16 (Sail.BitVec.extractLsb w__14 15 0)
              w__15) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__16)))
      | 32 =>
        (do
          let op32 ← (( do
            if (op1_neg : Bool)
            then
              (do
                let w__17 ← (( do (S_read n) ) : SailM (BitVec 32) )
                (FPNeg w__17))
            else
              (do
                (S_read n)) ) : SailM (BitVec 32) )
          let w__20 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__21 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__22 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__23 ← (( do (FPMulAdd w__20 op32 w__21 w__22) ) : SailM (BitVec 32) )
          (S_set d w__23))
      | 64 =>
        (do
          let op64 ← (( do
            if (op1_neg : Bool)
            then
              (do
                let w__24 ← (( do (D_read n) ) : SailM (BitVec 64) )
                (FPNeg w__24))
            else
              (do
                (D_read n)) ) : SailM (BitVec 64) )
          let w__27 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__28 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__29 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__30 ← (( do (FPMulAdd w__27 op64 w__28 w__29) ) : SailM (BitVec 64) )
          (D_set d w__30))
      | _ => (pure (())))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFNMA_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  let op16 ← (( do (undefined_bitvector_at (← occLabel 3435) 16) ) : SailM (BitVec 16) )
  let op32 ← (( do (undefined_bitvector_at (← occLabel 3436) 32) ) : SailM (BitVec 32) )
  let op64 ← (( do (undefined_bitvector_at (← occLabel 3437) 64) ) : SailM (BitVec 64) )
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let op16 ← (( do
        if (op1_neg : Bool)
        then
          (do
            let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
            (FPNeg (Sail.BitVec.extractLsb w__0 15 0)))
        else
          (do
            let w__2 ← (( do (S_read n) ) : SailM (BitVec 32) )
            (pure ((Sail.BitVec.extractLsb w__2 15 0)))) ) : SailM (BitVec 16) )
      let w__3 ← (( do (S_read d) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPNeg (Sail.BitVec.extractLsb w__3 15 0)) ) : SailM (BitVec 16) )
      let w__5 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__6 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPMulAdd w__4 op16 (Sail.BitVec.extractLsb w__5 15 0) w__6) ) : SailM
        (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__7)))
  | 32 =>
    (do
      let op32 ← (( do
        if (op1_neg : Bool)
        then
          (do
            let w__8 ← (( do (S_read n) ) : SailM (BitVec 32) )
            (FPNeg w__8))
        else
          (do
            (S_read n)) ) : SailM (BitVec 32) )
      let w__11 ← (( do (S_read d) ) : SailM (BitVec 32) )
      let w__12 ← (( do (FPNeg w__11) ) : SailM (BitVec 32) )
      let w__13 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__14 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__15 ← (( do (FPMulAdd w__12 op32 w__13 w__14) ) : SailM (BitVec 32) )
      (S_set d w__15))
  | 64 =>
    (do
      let op64 ← (( do
        if (op1_neg : Bool)
        then
          (do
            let w__16 ← (( do (D_read n) ) : SailM (BitVec 64) )
            (FPNeg w__16))
        else
          (do
            (D_read n)) ) : SailM (BitVec 64) )
      let w__19 ← (( do (D_read d) ) : SailM (BitVec 64) )
      let w__20 ← (( do (FPNeg w__19) ) : SailM (BitVec 64) )
      let w__21 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__22 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__23 ← (( do (FPMulAdd w__20 op64 w__21 w__22) ) : SailM (BitVec 64) )
      (D_set d w__23))
  | _ => (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, k_maximum : Bool, n : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAX_f_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3456)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3457)
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
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                if (maximum : Bool)
                then
                  (do
                    let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__6 ← (( do (FPMax op1 op2 w__5) ) : SailM (BitVec esize) )
                    let w__7 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                        (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__7))
                else
                  (do
                    let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__9 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__10 ← (( do (FPMin op1 op2 w__9) ) : SailM (BitVec esize) )
                    let w__11 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                        (Sail.BitVec.castWidth w__10))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__11))
                (pure ((op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


end ArmFull.Functions
