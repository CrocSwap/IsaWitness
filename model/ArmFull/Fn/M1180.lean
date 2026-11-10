import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0175
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0580
import ArmFull.Fn.M0925
import ArmFull.Fn.M1142
import ArmFull.Fn.M1146

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

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, m : Nat, n
  : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_a_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let esize : Nat := (Sail.Int.toNatChecked ((ebytes *i 8)))
  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> ((MemU_read address ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address ebytes) ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let element3 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes))) ) :
    SailM (BitVec (Sail.Int.toNatChecked esize)) )
  let element4 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes))) ) :
    SailM (BitVec (Sail.Int.toNatChecked esize)) )
  (D_set d
    (Sail.BitVec.castWidth (BitVec.replicateBits element1
      (Sail.Int.toNatChecked ((Int.ediv 64 esize))))))
  (D_set d2
    (Sail.BitVec.castWidth (BitVec.replicateBits element2
      (Sail.Int.toNatChecked ((Int.ediv 64 esize))))))
  (D_set d3
    (Sail.BitVec.castWidth (BitVec.replicateBits element3
      (Sail.Int.toNatChecked ((Int.ediv 64 esize))))))
  (D_set d4
    (Sail.BitVec.castWidth (BitVec.replicateBits element4
      (Sail.Int.toNatChecked ((Int.ediv 64 esize))))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__1 + w__2)))
      else
        (do
          let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__3 (4 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, d4__arg : Int, ebytes
  : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧
  0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (d4__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  let d4 : Int := d4__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let address ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := address
      for e in [loop_e_lower:loop_e_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) : SailM
            (BitVec (8 * ebytes)) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 e (Sail.Int.toNatChecked ((8 *i ebytes)))
              (Sail.BitVec.castWidth w__2))) ) : SailM (BitVec 64) )
          (D_set d w__3)
          let w__4 ← (( do (D_read d2) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address ebytes) ebytes)) ) :
            SailM (BitVec (8 * ebytes)) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e (Sail.Int.toNatChecked ((8 *i ebytes)))
              (Sail.BitVec.castWidth w__5))) ) : SailM (BitVec 64) )
          (D_set d2 w__6)
          let w__7 ← (( do (D_read d3) ) : SailM (BitVec 64) )
          let w__8 ← (( do
            ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes))
            ) : SailM (BitVec (8 * ebytes)) )
          let w__9 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e (Sail.Int.toNatChecked ((8 *i ebytes)))
              (Sail.BitVec.castWidth w__8))) ) : SailM (BitVec 64) )
          (D_set d3 w__9)
          let w__10 ← (( do (D_read d4) ) : SailM (BitVec 64) )
          let w__11 ← (( do
            ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes))
            ) : SailM (BitVec (8 * ebytes)) )
          let w__12 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e (Sail.Int.toNatChecked ((8 *i ebytes)))
              (Sail.BitVec.castWidth w__11))) ) : SailM (BitVec 64) )
          (D_set d4 w__12)
          let address : (BitVec 32) := (BitVec.addInt address (4 *i ebytes))
          (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__13 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__14 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__13 + w__14)))
      else
        (do
          let w__15 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__15 32))))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, d : Nat, n : Nat, regs : Int, k_single_regs : Bool, k_wback :
  Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLDM_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (regs : Int) (single_regs : Bool) (wback : Bool) : SailM Unit := do
  let word1 ← (( do (undefined_bitvector_at (← occLabel 3450) 32) ) : SailM (BitVec 32) )
  let word2 ← (( do (undefined_bitvector_at (← occLabel 3451) 32) ) : SailM (BitVec 32) )
  (CheckVFPEnabled true)
  let address ← (( do
    if (add : Bool)
    then
      (do
        (R_read n))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let (address, word1, word2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (regs -i 1)
    (do
      let mut loop_vars := (address, word1, word2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (address, word1, word2) := loop_vars
        loop_vars ← do
          if (single_regs : Bool)
          then
            (do
              let w__2 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
              (S_set (d +i r) w__2)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure ((address, word1, word2))))
          else
            (do
              let w__3 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
              let word1 := (w__3 : (BitVec 32))
              let w__4 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec (8 * 4))
                )
              let word2 := (w__4 : (BitVec 32))
              let address : (BitVec 32) := (BitVec.addInt address 8)
              let w__5 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
              let w__6 : (BitVec 64) :=
                if (w__5 : Bool)
                then (word1 +++ word2)
                else (word2 +++ word1)
              (D_set (d +i r) w__6)
              (pure ((address, word1, word2))))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) )
  if (wback : Bool)
  then
    (do
      let w__9 ← (( do
        if (add : Bool)
        then
          (do
            let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
            (pure ((w__7 + imm32))))
        else
          (do
            let w__8 ← (( do (R_read n) ) : SailM (BitVec 32) )
            (pure ((w__8 - imm32)))) ) : SailM (BitVec 32) )
      (R_set n w__9))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLDR_Op_A_txt (add : Bool) (d : Nat) (esize : Nat) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let word1 ← (( do (undefined_bitvector_at (← occLabel 3452) 32) ) : SailM (BitVec 32) )
  let word2 ← (( do (undefined_bitvector_at (← occLabel 3453) 32) ) : SailM (BitVec 32) )
  (CheckVFPEnabled true)
  let base ← (( do
    if ((n == 15) : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure ((Align_bits w__0 4))))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  match esize with
  | 16 =>
    (do
      let w__2 ← (( do (MemA_read address 2) ) : SailM (BitVec (8 * 2)) )
      (S_set d ((Zeros (n := 16)) +++ w__2)))
  | 32 =>
    (do
      let w__3 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
      (S_set d w__3))
  | 64 =>
    (do
      let word1 ← (( do (MemA_read address 4) ) : SailM (BitVec 32) )
      let word2 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec 32) )
      let w__4 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
      let w__5 : (BitVec 64) :=
        if (w__4 : Bool)
        then (word1 +++ word2)
        else (word2 +++ word1)
      (D_set d w__5))
  | _ => (pure (()))


def decode_aarch32_instrs_VRECPS_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRECPS_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRECPS_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((sz == 1#1) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRECPS_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRSQRTS_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSQRTS_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


def decode_aarch32_instrs_VRSQRTS_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__2 ← (( do
        if (((sz == 1#1) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let esize : Int := 16
      let elements : Int := 2
      let (elements, esize) : (Int × Int) :=
        match sz with
        | 0 =>
          (let esize : Int := 32
          let elements : Int := 2
          (elements, esize))
        | _ =>
          (let esize : Int := 16
          let elements : Int := 4
          (elements, esize))
      let esize : Int := esize
      let elements : Int := elements
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSQRTS_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index
  : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4] -/
def execute_aarch32_instrs_VST1_1_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set address ebytes (Sail.BitVec.castWidth w__2))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__4 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__3 + w__4)))
      else
        (do
          let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__5 ebytes))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index
  : Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2, 3, 4] ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST1_m_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let address ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := address
      for r in [loop_r_lower:loop_r_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := address
            for e in [loop_e_lower:loop_e_upper:1]i do
              let address := loop_vars_1
              loop_vars_1 ← do
                if ((ebytes != 8) : Bool)
                then
                  (do
                    let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__2 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e
                        (Sail.Int.toNatChecked ((8 *i ebytes))))) ) : SailM (BitVec (8 * ebytes)) )
                    (MemU_set address ebytes (Sail.BitVec.castWidth w__2)))
                else
                  (do
                    let w__4 ← (( do
                      if (((! (IsAligned__1 address ebytes)) : Bool) : Bool)
                      then
                        (do
                          (AlignmentEnforced ()))
                      else (pure false) ) : SailM Bool )
                    if (w__4 : Bool)
                    then
                      (do
                        let w__5 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                        (AArch32_Abort address w__5))
                    else (pure (()))
                    let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let data ← (( do (Elem_read w__6 e 64) ) : SailM (BitVec 64) )
                    let w__7 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
                    if (w__7 : Bool)
                    then
                      (do
                        (MemU_set address 4 (Sail.BitVec.extractLsb data 63 32))
                        (MemU_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb data 31 0)))
                    else
                      (do
                        (MemU_set address 4 (Sail.BitVec.extractLsb data 31 0))
                        (MemU_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb data 63 32))))
                let address : (BitVec 32) := (BitVec.addInt address ebytes)
                (pure (address))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__8 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__9 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__8 + w__9)))
      else
        (do
          let w__10 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__10 (8 *i regs)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, index : Nat, m : Nat, n :
  Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VST2_1_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set address ebytes (Sail.BitVec.castWidth w__2))
  let w__3 ← (( do (D_read d2) ) : SailM (BitVec 64) )
  let w__4 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set (BitVec.addInt address ebytes) ebytes (Sail.BitVec.castWidth w__4))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__6 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__5 + w__6)))
      else
        (do
          let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__7 (2 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, elements : Int, m : Nat, n :
  Nat, pairs : Nat, k_register_index : Bool, k_wback : Bool, List.elem pairs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST2_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (pairs : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let address ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((pairs -i 1)))
    (do
      let mut loop_vars := address
      for r in [loop_r_lower:loop_r_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := address
            for e in [loop_e_lower:loop_e_upper:1]i do
              let address := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e
                    (Sail.Int.toNatChecked ((8 *i ebytes))))) ) : SailM (BitVec (8 * ebytes)) )
                (MemU_set address ebytes (Sail.BitVec.castWidth w__2))
                let w__3 ← (( do (D_read (d2 +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e
                    (Sail.Int.toNatChecked ((8 *i ebytes))))) ) : SailM (BitVec (8 * ebytes)) )
                (MemU_set (BitVec.addInt address ebytes) ebytes (Sail.BitVec.castWidth w__4))
                let address : (BitVec 32) := (BitVec.addInt address (2 *i ebytes))
                (pure (address))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__6 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__5 + w__6)))
      else
        (do
          let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__7 (16 *i pairs)))))
  else (pure (()))


end ArmFull.Functions
