import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0154
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0186
import ArmFull.Fn.M0195
import ArmFull.Fn.M0197
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0216
import ArmFull.Fn.M0220
import ArmFull.Fn.M0237
import ArmFull.Fn.M0250
import ArmFull.Fn.M0254
import ArmFull.Fn.M0580
import ArmFull.Fn.M0925
import ArmFull.Fn.M1142

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

/-- Type quantifiers: d : Nat, d2 : Int, d3 : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index
  : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VST3_1_Op_A_txt (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set address ebytes (Sail.BitVec.castWidth w__1))
  let w__2 ← (( do (D_read d2) ) : SailM (BitVec 64) )
  let w__3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set (BitVec.addInt address ebytes) ebytes (Sail.BitVec.castWidth w__3))
  let w__4 ← (( do (D_read d3) ) : SailM (BitVec 64) )
  let w__5 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (Sail.BitVec.castWidth w__5))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__6 + w__7)))
      else
        (do
          let w__8 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__8 (3 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, ebytes : Nat, elements : Int, m
  : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 8] -/
def execute_aarch32_instrs_VST3_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
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
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := address
      for e in [loop_e_lower:loop_e_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set address ebytes (Sail.BitVec.castWidth w__2))
          let w__3 ← (( do (D_read d2) ) : SailM (BitVec 64) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set (BitVec.addInt address ebytes) ebytes (Sail.BitVec.castWidth w__4))
          let w__5 ← (( do (D_read d3) ) : SailM (BitVec 64) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (Sail.BitVec.castWidth w__6))
          let address : (BitVec 32) := (BitVec.addInt address (3 *i ebytes))
          (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__8 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__7 + w__8)))
      else
        (do
          let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__9 24))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, index :
  Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST4_1_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
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
  let w__5 ← (( do (D_read d3) ) : SailM (BitVec 64) )
  let w__6 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (Sail.BitVec.castWidth w__6))
  let w__7 ← (( do (D_read d4) ) : SailM (BitVec 64) )
  let w__8 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 index (Sail.Int.toNatChecked ((8 *i ebytes))))) )
    : SailM (BitVec (8 * ebytes)) )
  (MemU_set (BitVec.addInt address (3 *i ebytes)) ebytes (Sail.BitVec.castWidth w__8))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__10 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__9 + w__10)))
      else
        (do
          let w__11 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__11 (4 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, elements
  : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST4_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
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
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := address
      for e in [loop_e_lower:loop_e_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set address ebytes (Sail.BitVec.castWidth w__2))
          let w__3 ← (( do (D_read d2) ) : SailM (BitVec 64) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set (BitVec.addInt address ebytes) ebytes (Sail.BitVec.castWidth w__4))
          let w__5 ← (( do (D_read d3) ) : SailM (BitVec 64) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (Sail.BitVec.castWidth w__6))
          let w__7 ← (( do (D_read d4) ) : SailM (BitVec 64) )
          let w__8 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e (Sail.Int.toNatChecked ((8 *i ebytes)))))
            ) : SailM (BitVec (8 * ebytes)) )
          (MemU_set (BitVec.addInt address (3 *i ebytes)) ebytes (Sail.BitVec.castWidth w__8))
          let address : (BitVec 32) := (BitVec.addInt address (4 *i ebytes))
          (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__10 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__9 + w__10)))
      else
        (do
          let w__11 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__11 32))))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, d : Nat, n : Nat, regs : Int, k_single_regs : Bool, k_wback :
  Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSTM_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (regs : Int) (single_regs : Bool) (wback : Bool) : SailM Unit := do
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
  let address ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (regs -i 1)
    (do
      let mut loop_vars := address
      for r in [loop_r_lower:loop_r_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          if (single_regs : Bool)
          then
            (do
              let w__2 ← (( do (S_read (d +i r)) ) : SailM (BitVec 32) )
              (MemA_set address 4 w__2)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address)))
          else
            (do
              let w__3 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  (MemA_set address 4 (Sail.BitVec.extractLsb w__4 63 32))
                  let w__5 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb w__5 31 0)))
              else
                (do
                  let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  (MemA_set address 4 (Sail.BitVec.extractLsb w__6 31 0))
                  let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb w__7 63 32)))
              let address : (BitVec 32) := (BitVec.addInt address 8)
              (pure (address)))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      let w__10 ← (( do
        if (add : Bool)
        then
          (do
            let w__8 ← (( do (R_read n) ) : SailM (BitVec 32) )
            (pure ((w__8 + imm32))))
        else
          (do
            let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
            (pure ((w__9 - imm32)))) ) : SailM (BitVec 32) )
      (R_set n w__10))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSTR_Op_A_txt (add : Bool) (d : Nat) (esize : Nat) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  match esize with
  | 16 =>
    (do
      let w__2 ← (( do (S_read d) ) : SailM (BitVec 32) )
      (MemA_set address 2 (Sail.BitVec.extractLsb w__2 15 0)))
  | 32 =>
    (do
      let w__3 ← (( do (S_read d) ) : SailM (BitVec 32) )
      (MemA_set address 4 w__3))
  | 64 =>
    (do
      let w__4 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do (D_read d) ) : SailM (BitVec 64) )
          (MemA_set address 4 (Sail.BitVec.extractLsb w__5 63 32))
          let w__6 ← (( do (D_read d) ) : SailM (BitVec 64) )
          (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb w__6 31 0)))
      else
        (do
          let w__7 ← (( do (D_read d) ) : SailM (BitVec 64) )
          (MemA_set address 4 (Sail.BitVec.extractLsb w__7 31 0))
          let w__8 ← (( do (D_read d) ) : SailM (BitVec 64) )
          (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb w__8 63 32))))
  | _ => (pure (()))


/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wback : Bool, k_wordhigher : Bool, 0 ≤ n
  ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_e_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 15)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 3777) 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int_at (← occLabel 3778) ()) ) : SailM Int )
  let new_pc_value ← (( do (undefined_bitvector_at (← occLabel 3779) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let length : Int := ((4 *i (BitCount registers)) +i 4)
          let w__6 ← (( do
            if (increment_name : Bool)
            then
              (do
                (R_read n))
            else
              (do
                let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
                (pure ((BitVec.subInt w__5 length)))) ) : SailM (BitVec 32) )
          let address : (BitVec 32) := (w__6 : (BitVec 32))
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 14
            (do
              let mut loop_vars := address
              for i in [loop_i_lower:loop_i_upper:1]i do
                let address := loop_vars
                loop_vars ← do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                           (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
                  then
                    (do
                      let w__7 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
                      (R_set i w__7)
                      let address : (BitVec 32) := (BitVec.addInt address 4)
                      (pure (address)))
                  else (pure (address))
              (pure loop_vars)) ) : SailM (BitVec 32) )
          let new_pc_value ← (( do (MemS_read address 4) ) : SailM (BitVec 32) )
          ArmFull.assert ((0 ≤b n) && (n <b 15)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:40979.46-40979.47"
          if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 0#1)) : Bool)
          then
            (do
              let w__10 ← (( do
                if (increment_name : Bool)
                then
                  (do
                    let w__8 ← (( do (R_read n) ) : SailM (BitVec 32) )
                    (pure ((BitVec.addInt w__8 length))))
                else
                  (do
                    let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
                    (pure ((BitVec.subInt w__9 length)))) ) : SailM (BitVec 32) )
              (R_set n w__10))
          else (pure (()))
          if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 1#1)) : Bool)
          then
            (do
              let w__11 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
              (R_set n w__11))
          else (pure (()))
          let w__12 ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
          (AArch32_ExceptionReturn new_pc_value w__12)))


/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_u_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 15)) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 3780) 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int_at (← occLabel 3781) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let length : Int := (4 *i (BitCount registers))
          let w__6 ← (( do
            if (increment_name : Bool)
            then
              (do
                (R_read n))
            else
              (do
                let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
                (pure ((BitVec.subInt w__5 length)))) ) : SailM (BitVec 32) )
          let address : (BitVec 32) := (w__6 : (BitVec 32))
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 14
            (do
              let mut loop_vars := address
              for i in [loop_i_lower:loop_i_upper:1]i do
                let address := loop_vars
                loop_vars ← do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                           (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
                  then
                    (do
                      let w__7 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
                      (Rmode_set i M32_User w__7)
                      let address : (BitVec 32) := (BitVec.addInt address 4)
                      (pure (address)))
                  else (pure (address))
              (pure loop_vars)) ) : SailM (BitVec 32) )
          (pure (()))))


/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wback : Bool, k_wordhigher : Bool, 0 ≤ n
  ∧ n ≤ 15 -/
def execute_aarch32_instrs_RFE_Op_AS_txt (increment_name : Bool) (n : Nat) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 3787) 32) ) : SailM (BitVec 32) )
  let new_pc_value ← (( do (undefined_bitvector_at (← occLabel 3788) 32) ) : SailM (BitVec 32) )
  let spsr ← (( do (undefined_bitvector_at (← occLabel 3789) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let w__4 ← (( do
            if (increment_name : Bool)
            then
              (do
                (R_read n))
            else
              (do
                let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
                (pure ((BitVec.subInt w__3 8)))) ) : SailM (BitVec 32) )
          let address : (BitVec 32) := (w__4 : (BitVec 32))
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let new_pc_value ← (( do (MemA_read address 4) ) : SailM (BitVec 32) )
          let spsr ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec 32) )
          if (wback : Bool)
          then
            (do
              let w__7 ← (( do
                if (increment_name : Bool)
                then
                  (do
                    let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
                    (pure ((BitVec.addInt w__5 8))))
                else
                  (do
                    let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
                    (pure ((BitVec.subInt w__6 8)))) ) : SailM (BitVec 32) )
              (R_set n w__7))
          else (pure (()))
          (AArch32_ExceptionReturn new_pc_value spsr)))


/-- Type quantifiers: k_increment_name : Bool, k_wback : Bool, k_wordhigher : Bool -/
def execute_aarch32_instrs_SRS_OpA_AS_txt (increment_name : Bool) (mode : (BitVec 5)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__1.M == M32_User) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else
    (do
      if ((mode == M32_Hyp) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          if ((mode == M32_Monitor) : Bool)
          then
            (do
              let w__5 ← (( do
                if (((! (HaveEL EL3)) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__4 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                    (pure (((bne w__4 SS_Secure) : Bool)))) ) : SailM Bool )
              if (w__5 : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  if ((! w__6) : Bool)
                  then
                    (do
                      (AArch64_MonitorModeTrap ()))
                  else (pure (()))))
          else
            (do
              let w__7 ← (( do (BadMode mode) ) : SailM Bool )
              if (w__7 : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else (pure (())))))
  let base ← (( do (Rmode_read 13 mode) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (increment_name : Bool)
    then base
    else (BitVec.subInt base 8)
  let address : (BitVec 32) :=
    if (wordhigher : Bool)
    then (BitVec.addInt address 4)
    else address
  let w__8 ← (( do (LR_read ()) ) : SailM (BitVec 32) )
  (MemA_set address 4 w__8)
  let w__9 ← (( do (SPSR_read (N := (Sail.Int.toNatChecked ((8 *i 4))))) ) : SailM
    (BitVec (8 * 4)) )
  (MemA_set (BitVec.addInt address 4) 4 w__9)
  if (wback : Bool)
  then
    (do
      (Rmode_set 13 mode
        (if (increment_name : Bool)
        then (BitVec.addInt base 8)
        else (BitVec.subInt base 8))))
  else (pure (()))


/-- Type quantifiers: k_increment_name : Bool, k_wback : Bool, k_wordhigher : Bool -/
def execute_aarch32_instrs_SRS_OpT_AS_txt (increment_name : Bool) (mode : (BitVec 5)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__1.M == M32_User) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else
    (do
      if ((mode == M32_Hyp) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          if ((mode == M32_Monitor) : Bool)
          then
            (do
              let w__5 ← (( do
                if (((! (HaveEL EL3)) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__4 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                    (pure (((bne w__4 SS_Secure) : Bool)))) ) : SailM Bool )
              if (w__5 : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  if ((! w__6) : Bool)
                  then
                    (do
                      (AArch64_MonitorModeTrap ()))
                  else (pure (()))))
          else
            (do
              let w__7 ← (( do (BadMode mode) ) : SailM Bool )
              if (w__7 : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else (pure (())))))
  let base ← (( do (Rmode_read 13 mode) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (increment_name : Bool)
    then base
    else (BitVec.subInt base 8)
  let address : (BitVec 32) :=
    if (wordhigher : Bool)
    then (BitVec.addInt address 4)
    else address
  let w__8 ← (( do (LR_read ()) ) : SailM (BitVec 32) )
  (MemA_set address 4 w__8)
  let w__9 ← (( do (SPSR_read (N := (Sail.Int.toNatChecked ((8 *i 4))))) ) : SailM
    (BitVec (8 * 4)) )
  (MemA_set (BitVec.addInt address 4) 4 w__9)
  if (wback : Bool)
  then
    (do
      (Rmode_set 13 mode
        (if (increment_name : Bool)
        then (BitVec.addInt base 8)
        else (BitVec.subInt base 8))))
  else (pure (()))


end ArmFull.Functions
