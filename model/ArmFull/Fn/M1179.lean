import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0124
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0243
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

/-- Type quantifiers: k_is_tbh : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TBB_Op_A_txt (is_tbh : Bool) (m : Nat) (n : Nat) : SailM Unit := do
  let halfwords ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3296) 0 65535))) ) :
    SailM Nat )
  let halfwords ← (( do
    if (is_tbh : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let w__2 ← (( do (MemU_read (w__0 + (w__1 <<< 1)) 2) ) : SailM (BitVec (8 * 2)) )
        let halfwords : Nat := ((BitVec.toNat w__2) : Nat)
        (pure (halfwords)))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__4 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let w__5 ← (( do (MemU_read (w__3 + w__4) 1) ) : SailM (BitVec (8 * 1)) )
        let halfwords : Nat := ((BitVec.toNat w__5) : Nat)
        (pure (halfwords))) ) : SailM Nat )
  let halfwords : Int := halfwords
  let w__6 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
  (BranchWritePC (BitVec.addInt w__6 (2 *i halfwords)) BranchType_INDIR)


/-- Type quantifiers: alignment : Nat, d__arg : Nat, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index
  : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 2, 4] -/
def execute_aarch32_instrs_VLD1_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
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
  let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__2))) ) : SailM (BitVec 64) )
  (D_set d w__3)
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__4 + w__5)))
      else
        (do
          let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__6 ebytes))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, m : Nat, n : Nat, k_register_index :
  Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VLD1_a_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
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
  let esize : Nat := (Sail.Int.toNatChecked ((8 *i ebytes)))
  let element ← (( do ((Sail.BitVec.castWidth ) <$> ((MemU_read address ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let replicated_element : (BitVec 64) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits element
      (Sail.Int.toNatChecked ((Int.ediv 64 esize)))))
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do (D_set (d +i r) replicated_element)
    (pure loop_vars))
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
          (R_set n (BitVec.addInt w__3 ebytes))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index
  : Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2, 3, 4] ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧
  0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD1_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
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
                let data ← (( do
                  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3447)
                    (Sail.Int.toNatChecked ((ebytes *i 8))))) ) : SailM (BitVec (ebytes * 8)) )
                let data ← (( do
                  if ((ebytes != 8) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)))
                  else
                    (do
                      let w__3 ← (( do
                        if (((! (IsAligned__1 address ebytes)) : Bool) : Bool)
                        then
                          (do
                            (AlignmentEnforced ()))
                        else (pure false) ) : SailM Bool )
                      if (w__3 : Bool)
                      then
                        (do
                          let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                          (AArch32_Abort address w__4))
                      else (pure (()))
                      let w__5 ← (( do (BigEndian AccessType_ASIMD) ) : SailM Bool )
                      if (w__5 : Bool)
                      then
                        (do
                          let w__6 ← (( do (MemU_read (BitVec.addInt address 4) 4) ) : SailM
                            (BitVec (8 * 4)) )
                          let data :=
                            ((Sail.BitVec.updateSubrange data 31 0 w__6) : (BitVec (ebytes * 8)))
                          let w__7 ← (( do (MemU_read address 4) ) : SailM (BitVec (8 * 4)) )
                          let data :=
                            ((Sail.BitVec.updateSubrange data 63 32 w__7) : (BitVec (ebytes * 8)))
                          (pure (data)))
                      else
                        (do
                          let w__8 ← (( do (MemU_read address 4) ) : SailM (BitVec (8 * 4)) )
                          let data :=
                            ((Sail.BitVec.updateSubrange data 31 0 w__8) : (BitVec (ebytes * 8)))
                          let w__9 ← (( do (MemU_read (BitVec.addInt address 4) 4) ) : SailM
                            (BitVec (8 * 4)) )
                          let data :=
                            ((Sail.BitVec.updateSubrange data 63 32 w__9) : (BitVec (ebytes * 8)))
                          (pure (data)))) ) : SailM (BitVec (ebytes * 8)) )
                let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__11 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e
                    (Sail.Int.toNatChecked ((8 *i ebytes))) (Sail.BitVec.castWidth data))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__11)
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
          let w__12 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__13 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__12 + w__13)))
      else
        (do
          let w__14 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__14 (8 *i regs)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, ebytes : Nat, index : Nat, m :
  Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VLD2_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
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
  let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__2))) ) : SailM (BitVec 64) )
  (D_set d w__3)
  let w__4 ← (( do (D_read d2) ) : SailM (BitVec 64) )
  let w__5 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address ebytes) ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__6 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__5))) ) : SailM (BitVec 64) )
  (D_set d2 w__6)
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
          (R_set n (BitVec.addInt w__9 (2 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, m : Nat, n : Nat, k_register_index
  : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8, 16] -/
def execute_aarch32_instrs_VLD2_a_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
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
  let esize : Nat := (Sail.Int.toNatChecked ((8 *i ebytes)))
  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> ((MemU_read address ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address ebytes) ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  (D_set d
    (Sail.BitVec.castWidth (BitVec.replicateBits element1
      (Sail.Int.toNatChecked ((Int.ediv 64 esize))))))
  (D_set d2
    (Sail.BitVec.castWidth (BitVec.replicateBits element2
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
          (R_set n (BitVec.addInt w__3 (2 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, ebytes : Nat, elements : Int, m
  : Nat, n : Nat, pairs : Nat, k_register_index : Bool, k_wback : Bool, List.elem pairs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧
  0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD2_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (pairs : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
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
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) :
                  SailM (BitVec (8 * ebytes)) )
                let w__3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 e
                    (Sail.Int.toNatChecked ((8 *i ebytes))) (Sail.BitVec.castWidth w__2))) ) : SailM
                  (BitVec 64) )
                (D_set (d +i r) w__3)
                let w__4 ← (( do (D_read (d2 +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address ebytes) ebytes)) )
                  : SailM (BitVec (8 * ebytes)) )
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e
                    (Sail.Int.toNatChecked ((8 *i ebytes))) (Sail.BitVec.castWidth w__5))) ) : SailM
                  (BitVec 64) )
                (D_set (d2 +i r) w__6)
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
          let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__8 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__7 + w__8)))
      else
        (do
          let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__9 (16 *i pairs)))))
  else (pure (()))


/-- Type quantifiers: d__arg : Nat, d2__arg : Int, d3__arg : Int, ebytes : Nat, index : Nat, m : Nat, n
  : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VLD3_1_Op_A_txt (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__1))) ) : SailM (BitVec 64) )
  (D_set d w__2)
  let w__3 ← (( do (D_read d2) ) : SailM (BitVec 64) )
  let w__4 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address ebytes) ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__5 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__4))) ) : SailM (BitVec 64) )
  (D_set d2 w__5)
  let w__6 ← (( do (D_read d3) ) : SailM (BitVec 64) )
  let w__7 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)) ) :
    SailM (BitVec (8 * ebytes)) )
  let w__8 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__7))) ) : SailM (BitVec 64) )
  (D_set d3 w__8)
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
          (R_set n (BitVec.addInt w__11 (3 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: d : Nat, d2 : Int, d3 : Int, ebytes : Nat, m : Nat, n : Nat, k_register_index
  : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLD3_a_Op_A_txt (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let esize : Nat := (Sail.Int.toNatChecked ((ebytes *i 8)))
  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> ((MemU_read address ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address ebytes) ebytes))) ) : SailM
    (BitVec (Sail.Int.toNatChecked esize)) )
  let element3 ← (( do
    ((Sail.BitVec.castWidth ) <$> ((MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes))) ) :
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
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__0 + w__1)))
      else
        (do
          let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__2 (3 *i ebytes)))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, ebytes : Nat, elements
  : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 8] -/
def execute_aarch32_instrs_VLD3_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
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
          let address : (BitVec 32) := (BitVec.addInt address (3 *i ebytes))
          (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then
        (do
          let w__10 ← (( do (R_read n) ) : SailM (BitVec 32) )
          let w__11 ← (( do (R_read m) ) : SailM (BitVec 32) )
          (R_set n (w__10 + w__11)))
      else
        (do
          let w__12 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (R_set n (BitVec.addInt w__12 24))))
  else (pure (()))


/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, d4__arg : Int, ebytes
  : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem ebytes [1, 2, 4] ∧
  0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (d4__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
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
  let w__1 ← (( do (D_read d) ) : SailM (BitVec 64) )
  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (MemU_read address ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__2))) ) : SailM (BitVec 64) )
  (D_set d w__3)
  let w__4 ← (( do (D_read d2) ) : SailM (BitVec 64) )
  let w__5 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address ebytes) ebytes)) ) : SailM
    (BitVec (8 * ebytes)) )
  let w__6 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__5))) ) : SailM (BitVec 64) )
  (D_set d2 w__6)
  let w__7 ← (( do (D_read d3) ) : SailM (BitVec 64) )
  let w__8 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)) ) :
    SailM (BitVec (8 * ebytes)) )
  let w__9 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__8))) ) : SailM (BitVec 64) )
  (D_set d3 w__9)
  let w__10 ← (( do (D_read d4) ) : SailM (BitVec 64) )
  let w__11 ← (( do
    ((Sail.BitVec.castWidth ) <$> (MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes)) ) :
    SailM (BitVec (8 * ebytes)) )
  let w__12 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 index (Sail.Int.toNatChecked ((8 *i ebytes)))
      (Sail.BitVec.castWidth w__11))) ) : SailM (BitVec 64) )
  (D_set d4 w__12)
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
          (R_set n (BitVec.addInt w__15 (4 *i ebytes)))))
  else (pure (()))


end ArmFull.Functions
