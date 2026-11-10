import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0120
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0
  ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKPBS_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5460)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (LastActive mask operand1 8) ) : SailM (BitVec 1) )
  let last : Bool := (w__0 == 1#1)
  let (last, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (last, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, result) := loop_vars
        loop_vars ← do
          let w__1 ← (( do (ActivePredicateElement mask e 8) ) : SailM Bool )
          if (w__1 : Bool)
          then
            (do
              let w__3 ← (( do
                if ((last : Bool) : Bool)
                then
                  (do
                    let w__2 ← (( do (ActivePredicateElement operand2 e 8) ) : SailM Bool )
                    (pure (((! w__2) : Bool))))
                else (pure false) ) : SailM Bool )
              let last := (w__3 : Bool)
              let pbit : (BitVec 1) :=
                if (last : Bool)
                then 1#1
                else 0#1
              let w__4 ← (( do (Elem_set result e 1 (Sail.BitVec.zeroExtend pbit 1)) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__4 : (BitVec (Sail.Int.toNatChecked PL)))
              (pure ((last, result))))
          else
            (do
              let w__5 ← (( do (Elem_set result e 1 (Sail.BitVec.zeroExtend 0#1 1)) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__5 : (BitVec (Sail.Int.toNatChecked PL)))
              (pure ((last, result))))
      (pure loop_vars)) ) : SailM (Bool × (BitVec (Sail.Int.toNatChecked PL))) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dm : Nat, g : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ dm ∧ dm ≤ 15 ∧ (is_VL VL) -/
def execute_BRKN_P_P_PP__ (VL : Nat) (dm : Nat) (g : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read dm PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5461)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (LastActive mask operand1 8) ) : SailM (BitVec 1) )
  let result : (BitVec (Sail.Int.toNatChecked PL)) :=
    if ((w__0 == 1#1) : Bool)
    then operand2
    else (Sail.BitVec.castWidth (Zeros (n := PL)))
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest (Sail.BitVec.castWidth (Ones (n := PL))) result 8) ) : SailM
        (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set dm PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dm : Nat, g : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ dm ∧ dm ≤ 15 ∧ (is_VL VL) -/
def execute_BRKNS_P_P_PP__ (VL : Nat) (dm : Nat) (g : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read dm PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5462)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (LastActive mask operand1 8) ) : SailM (BitVec 1) )
  let result : (BitVec (Sail.Int.toNatChecked PL)) :=
    if ((w__0 == 1#1) : Bool)
    then operand2
    else (Sail.BitVec.castWidth (Zeros (n := PL)))
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest (Sail.BitVec.castWidth (Ones (n := PL))) result 8) ) : SailM
        (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set dm PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INSR_Z_V__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dest ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m esize)) ) : SailM (BitVec esize) )
  (Z_set dn VL
    (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb dest
        (Sail.Int.toNatChecked (((VL -i esize) -i 1))) 0) +++ src)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INSR_Z_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dest ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m esize)) ) : SailM (BitVec esize) )
  (Z_set dn VL
    (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb dest
        (Sail.Int.toNatChecked (((VL -i esize) -i 1))) 0) +++ src)))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5463)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5464)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5465)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5466)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toNat w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5467)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toNat w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5468)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toNat w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USDOT_Z_ZZZ_S (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5469)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5470)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toNat w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toInt w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SUDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5471)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element1 : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let element2 : Int := (BitVec.toNat w__1)
                  let res : (BitVec esize) := (BitVec.addInt res (element1 *i element2))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
