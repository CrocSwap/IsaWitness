import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0150
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M0925
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072
import ArmFull.Fn.M1077

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

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 1)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3872) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3873) 64) ) : SailM (BitVec 64) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3874)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3875)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result1, result2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, operand2, result1, result2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, operand2, result1, result2) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let (result1, result2) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := ((fdiv_int elements 2) -i 1)
            (do
              let mut loop_vars_1 := (result1, result2)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (result1, result2) := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3876)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let element3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3877)
                      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                  let (element1, element3) ← (( do
                    match rot with
                    | 0 =>
                      (do
                        let w__2 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let w__3 ← (( do (FPNeg w__2) ) : SailM (BitVec esize) )
                        let element1 := (w__3 : (BitVec esize))
                        let w__4 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let element3 := (w__4 : (BitVec esize))
                        (pure ((element1, element3))))
                    | _ =>
                      (do
                        let w__5 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((e *i 2) +i 1) esize))
                          ) : SailM (BitVec esize) )
                        let element1 := (w__5 : (BitVec esize))
                        let w__6 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e *i 2) esize)) ) :
                          SailM (BitVec esize) )
                        let w__7 ← (( do (FPNeg w__6) ) : SailM (BitVec esize) )
                        let element3 := (w__7 : (BitVec esize))
                        (pure ((element1, element3)))) ) : SailM ((BitVec esize) × (BitVec esize))
                    )
                  let element3 := element3
                  let element1 := element1
                  let w__8 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e *i 2) esize)) ) : SailM
                    (BitVec esize) )
                  let w__9 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__10 ← (( do (FPAdd w__8 element1 w__9) ) : SailM (BitVec esize) )
                  let result1 := (w__10 : (BitVec esize))
                  let w__11 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((e *i 2) +i 1) esize)) ) :
                    SailM (BitVec esize) )
                  let w__12 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__13 ← (( do (FPAdd w__11 element3 w__12) ) : SailM (BitVec esize) )
                  let result2 := (w__13 : (BitVec esize))
                  let w__14 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__15 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__14 (e *i 2) esize
                      (Sail.BitVec.castWidth result1))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__15)
                  let w__16 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__17 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__16 ((e *i 2) +i 1) esize
                      (Sail.BitVec.castWidth result2))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__17)
                  (pure ((result1, result2)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec esize)) )
          (pure ((operand1, operand2, result1, result2)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, k_sub_op :
  Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMAL_Op_A_txt (Q : (BitVec 1)) (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3878)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3879)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (undefined_bitvector_at (← occLabel 3880) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3881) 64) ) : SailM (BitVec 64) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3882)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3883)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let (operand1, operand2) ← (( do
    if ((Q == 0#1) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b (datasize -i 1)) && ((datasize -i 1) <b 32)) "sail-arm/instrs32.sail:46899.68-46899.69"
        let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
        let operand1 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
        let operand2 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        (pure ((operand1, operand2))))
    else
      (do
        let w__2 ← (( do (D_read n) ) : SailM (BitVec 64) )
        let operand1 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        let w__3 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let operand2 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__3
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        (pure ((operand1, operand2)))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  let (element1, element2, operand3, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (element1, element2, operand3, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (element1, element2, operand3, result) := loop_vars
        loop_vars ← do
          let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let operand3 := (w__4 : (BitVec 64))
          let (element1, element2, result) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := (element1, element2, result)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (element1, element2, result) := loop_vars_1
                loop_vars_1 ← do
                  let w__5 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i r) +i e)
                      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2))
                    )
                  let element1 := (w__5 : (BitVec (esize / 2)))
                  let w__6 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i r) +i e)
                      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2))
                    )
                  let element2 := (w__6 : (BitVec (esize / 2)))
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
                  let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec 32) )
                  let w__9 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__10 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) w__8
                      (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__9)) ) :
                    SailM (BitVec 32) )
                  let w__11 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__10)) ) :
                    SailM (BitVec 64) )
                  let result := (w__11 : (BitVec 64))
                  (pure ((element1, element2, result)))
              (pure loop_vars_1)) ) : SailM
            ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((element1, element2, operand3, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, regs :
  Nat, k_sub_op : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3] ∧
  esize = 32 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMAL_i_Op_A_txt (Q : (BitVec 1)) (d : Nat) (datasize : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3884)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3885)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (undefined_bitvector_at (← occLabel 3886) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3887) 64) ) : SailM (BitVec 64) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3888)
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let (operand1, operand2) ← (( do
    if ((Q == 0#1) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b (datasize -i 1)) && ((datasize -i 1) <b 32)) "sail-arm/instrs32.sail:47001.68-47001.69"
        let w__0 ← (( do (S_read n) ) : SailM (BitVec 32) )
        let operand1 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
        let operand2 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        (pure ((operand1, operand2))))
    else
      (do
        let w__2 ← (( do (D_read n) ) : SailM (BitVec 64) )
        let operand1 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        let w__3 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let operand2 :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__3
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)) : (BitVec datasize))
        (pure ((operand1, operand2)))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 index
      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
  let (element1, operand3, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (element1, operand3, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (element1, operand3, result) := loop_vars
        loop_vars ← do
          let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let operand3 := (w__4 : (BitVec 64))
          let (element1, result) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := (element1, result)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (element1, result) := loop_vars_1
                loop_vars_1 ← do
                  let w__5 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i r) +i e)
                      (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2))
                    )
                  let element1 := (w__5 : (BitVec (esize / 2)))
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
                  let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec 32) )
                  let w__8 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) w__7
                      (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__8)) ) :
                    SailM (BitVec 32) )
                  let w__10 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__9)) ) :
                    SailM (BitVec 64) )
                  let result := (w__10 : (BitVec 64))
                  (pure ((element1, result)))
              (pure loop_vars_1)) ) : SailM ((BitVec (esize / 2)) × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((element1, operand3, result)))
      (pure loop_vars)) ) : SailM ((BitVec (esize / 2)) × (BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let operand ← (( do (undefined_bitvector_at (← occLabel 3894) 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3895) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let _ : Unit := (EncodingSpecificOperations ())
      (CheckAdvSIMDEnabled ())
      let operand ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
      let result ← (( do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := 3
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let op ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
              let w__1 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
              let w__2 ← (( do (FPConvertBF__1 (k_N := 32) op w__1) ) : SailM (BitVec (32 / 2)) )
              (Elem_set result e 16 w__2)
          (pure loop_vars)) ) : SailM (BitVec 64) )
      (D_set d result))
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTB_bf16_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let w__0 ← (( do (S_read d) ) : SailM (BitVec 32) )
  let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
  let w__3 ← (( do (FPConvertBF__1 (k_N := 32) w__1 w__2) ) : SailM (BitVec (32 / 2)) )
  (S_set d (Sail.BitVec.updateSubrange w__0 15 0 w__3))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let w__0 ← (( do (S_read d) ) : SailM (BitVec 32) )
  let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
  let w__3 ← (( do (FPConvertBF__1 (k_N := 32) w__1 w__2) ) : SailM (BitVec (32 / 2)) )
  (S_set d (Sail.BitVec.updateSubrange w__0 31 16 w__3))


/-- Type quantifiers: d : Nat, elements : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMA_bf_Op_A_txt (d : Nat) (elements : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let operand3 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3896) 128) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let element1 : (BitVec 32) := (w__0 +++ (Zeros (n := 16)))
          let w__1 ← (( do (Elem_read operand2 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let element2 : (BitVec 32) := (w__1 +++ (Zeros (n := 16)))
          let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd addend element1 element2 w__2) ) : SailM (BitVec 32) )
          (Elem_set result e 32 w__3)
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) result)


/-- Type quantifiers: d : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel
  [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem i [0, 1, 2, 3] ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMA_bfs_Op_A_txt (d : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (D_read m) ) : SailM (BitVec 64) )
  let operand3 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3897) 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (Elem_read operand2 i 16) ) : SailM (BitVec 16) )
  let element2 : (BitVec 32) := (w__0 +++ (Zeros (n := 16)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let element1 : (BitVec 32) := (w__1 +++ (Zeros (n := 16)))
          let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd addend element1 element2 w__2) ) : SailM (BitVec 32) )
          (Elem_set result e 32 w__3)
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) result)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_cvt_bf16_scalar (d : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let w__1 ← (( do (FPConvertBF__1 (k_N := 32) operand fpcr) ) : SailM (BitVec (32 / 2)) )
  let w__2 ← (( do (Elem_set result 0 16 w__1) ) : SailM (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, elements : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧ n ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_cvt_bf16_vector (d : Nat) (elements : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3974) 64) ) : SailM (BitVec 64) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (FPConvertBF__1 (k_N := 32) w__0 w__1) ) : SailM (BitVec (32 / 2)) )
          (Elem_set result e 16 w__2)
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (Vpart_set d part 64 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n
  ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem i [0, 1, 2, 3] ∧
  List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_bfdot (d : Nat) (datasize : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3975)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
          let elt2_a ← (( do (Elem_read operand2 ((2 *i i) +i 0) 16) ) : SailM (BitVec 16) )
          let elt2_b ← (( do (Elem_read operand2 ((2 *i i) +i 1) 16) ) : SailM (BitVec 16) )
          let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let sum ← (( do (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 sum)
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot (d : Nat) (datasize : Nat) (elements : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3976)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
          let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
          let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let sum ← (( do (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 sum)
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, elements : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, List.elem
  sel [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long (d : Nat) (elements : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let result ← (( do (undefined_bitvector_at (← occLabel 3989) 128) ) : SailM (BitVec 128) )
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let element2 ← (( do (Elem_read operand2 index 16) ) : SailM (BitVec 16) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMulAddH (k_N := 32) addend element1 element2 w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 w__1)
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, elements : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long (d : Nat) (elements : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3990) 128) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
          let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMulAddH (k_N := 32) addend element1 element2 w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 w__1)
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


def decode_cas_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


def decode_casb_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) regsize release (Sail.Int.toNatChecked (s))
    (Sail.Int.toNatChecked (t)) tagchecked)


end ArmFull.Functions
