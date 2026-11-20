module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize
  : Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec (Sail.Int.toNatChecked PL)) := (Sail.BitVec.castWidth (Ones (n := PL)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5246)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5247) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 >b w__1) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≥b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM (Bool × (BitVec rsize) × (BitVec (Sail.Int.toNatChecked PL))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPEQ_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5248)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5249) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPNE_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5250)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5251) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ imm ∧
  imm ≤ 127 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHS_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5252)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5253) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ imm ∧
  imm ≤ 127 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHI_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5254)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5255) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ imm ∧
  imm ≤ 127 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLO_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5256)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5257) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ imm ∧
  imm ≤ 127 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLS_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5258)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5259) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGE_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5260)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5261) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGT_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5262)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let cond ← (( do (undefined_bool_at (← occLabel 5263) ()) ) : SailM Bool )
              let cond : Bool :=
                match op with
                | .Cmp_EQ => (element1 == imm)
                | .Cmp_NE => (element1 != imm)
                | .Cmp_GE => (element1 ≥b imm)
                | .Cmp_LT => (element1 <b imm)
                | .Cmp_GT => (element1 >b imm)
                | .Cmp_LE => (element1 ≤b imm)
                | _ => cond
              let pbit : (BitVec 1) :=
                if (cond : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
