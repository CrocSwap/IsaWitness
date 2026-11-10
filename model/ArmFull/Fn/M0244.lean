import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0058
import ArmFull.Fn.M0063
import ArmFull.Fn.M0066
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0099
import ArmFull.Fn.M0100
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0159
import ArmFull.Fn.M0164
import ArmFull.Fn.M0165
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0195
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0217
import ArmFull.Fn.M0219
import ArmFull.Fn.M0228
import ArmFull.Fn.M0241
import ArmFull.Fn.M0242
import ArmFull.Fn.M0243

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

def decode_dcps2_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)


def decode_dcps3_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)


def execute_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  (DRPSInstruction ())


def execute_aarch64_instrs_system_barriers_isb (_ : Unit) : SailM Unit := do
  (InstructionSynchronizationBarrier ())
  let w__2 ← (( do
    if ((← do
         (HaveBRBExt ())) : Bool)
    then
      (do
        (BRBEBranchOnISB ()))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (BRBEISB ()))
  else (pure (()))
  let w__3 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (SPEISB ()))
  else (pure (()))


/-- Type quantifiers: bit_pos : Nat, datasize : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ bit_pos ∧ bit_pos ≤ 63 -/
def execute_aarch64_instrs_branch_conditional_test (bit_pos : Nat) (bit_val : (BitVec 1)) (datasize : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (X_read t datasize)) ) : SailM
    (BitVec datasize) )
  let branch_conditional : Bool := true
  ArmFull.assert (bit_pos <b datasize) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:52130.43-52130.44"
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand bit_pos)])) == bit_val) : Bool)
  then
    (do
      let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (BranchTo (w__0 + offset) BranchType_DIR branch_conditional))
  else
    (do
      (BranchNotTaken BranchType_DIR branch_conditional))


/-- Type quantifiers: d : Nat, k_data : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_strip_dp_1src (d : Nat) (data : Bool) : SailM Unit := do
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__2 ← (( do (Strip w__1 data) ) : SailM (BitVec 64) )
      (X_set d 64 w__2))
  else (pure (()))


/-- Type quantifiers: k_retry : Bool -/
def FailTransaction (cause : TMFailure) (retry : Bool) : SailM Unit := do
  (FailTransaction__1 cause retry false (Zeros (n := 15)))


/-- Type quantifiers: size : Nat, size > 0 -/
def PhysMemRead (desc : AddressDescriptor) (size : Nat) (accdesc : AccessDescriptor) (translation_info : (Option TranslationInfo)) : SailM (PhysMemRetStatus × (BitVec (8 * size))) := do
  let paddress := desc.paddress.address
  if (((size ≥b 4) && ((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
           (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
           (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) GIC_BASE)))) : Bool)
  then
    (do
      let w__0 ← (( do (__ReadGIC (Sail.BitVec.extractLsb paddress 15 0)) ) : SailM (BitVec 32) )
      (pure (((CreatePhysMemRetStatus Fault_None), (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
          w__0 (Sail.Int.toNatChecked ((8 *i size)))))))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
             (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
             (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) UART_BASE))) : Bool)
      then
        (pure (((CreatePhysMemRetStatus Fault_None), (Sail.BitVec.castWidth (__ReadUART
            (Sail.BitVec.extractLsb paddress 15 0) size)))))
      else
        (do
          let w__1 ← (( do
            (sail_mem_read
              (read_request accdesc translation_info size desc.vaddress desc.paddress.address)) ) :
            SailM (Result ((BitVec (8 * size)) × (Option Bool)) Fault) )
          let w__2 : (PhysMemRetStatus × (BitVec (8 * size))) :=
            match w__1 with
            | .Ok (value, _) => ((CreatePhysMemRetStatus Fault_None), value)
            | .Err statuscode =>
              ((CreatePhysMemRetStatus statuscode), (Sail.BitVec.castWidth (BitVec.zero
                (Sail.Int.toNatChecked ((8 *i size))))))
          (pure (w__2))))


/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 64 -/
def AArch64_BreakpointMatch (n : Nat) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (size : Int) : SailM (Bool × Bool) := do
  let match_i ← (( do (undefined_bool_at (← occLabel 1389) ()) ) : SailM Bool )
  let valid_mismatch_name ← (( do (undefined_bool_at (← occLabel 1390) ()) ) : SailM Bool )
  let value_match_name ← (( do (undefined_bool_at (← occLabel 1391) ()) ) : SailM Bool )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert (! w__1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23603.61-23603.62"
  let w__2 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23604.42-23604.43"
  let linking_enabled ← (( do
    if ((← do
         let w__3 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
         let b__1 := (_get_DBGBCR_EL1_Type_BT (GetElem?.getElem! w__3 n))
         (pure ((if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                    b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
           then true
           else
             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                      b__1 0 0)) == (1#1 : (BitVec 1)))) : Bool)
             then true
             else false) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (HaveFeatABLE ())) : Bool)
        then
          (do
            let w__5 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((((_get_DBGBCR_EL1_Type_BT2 (GetElem?.getElem! w__5 n)) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (linking_enabled : Bool)
  then (pure ((false, false)))
  else
    (do
      let enabled ← (( do (IsBreakpointEnabled n) ) : SailM Bool )
      let w__7 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let b__0 := (_get_DBGBCR_EL1_Type_BT (GetElem?.getElem! w__7 n))
      let linked : Bool :=
        (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then true
        else false : Bool)
      let isbreakpnt : Bool := true
      let linked_to : Bool := false
      let w__8 ← (( do (Havev8p9Debug ()) ) : SailM Bool )
      let lbnx ← (( do
        if (w__8 : Bool)
        then
          (do
            let w__9 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((_get_DBGBCR_EL1_Type_LBNX (GetElem?.getElem! w__9 n)))))
        else (pure (0b00#2)) ) : SailM (BitVec 2) )
      let w__10 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let linked_n : Int :=
        (BitVec.toNat (lbnx +++ (_get_DBGBCR_EL1_Type_LBN (GetElem?.getElem! w__10 n))))
      let w__11 ← (( do (HaveRME ()) ) : SailM Bool )
      let ssce ← (( do
        if (w__11 : Bool)
        then
          (do
            let w__12 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((_get_DBGBCR_EL1_Type_SSCE (GetElem?.getElem! w__12 n)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let w__13 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let w__14 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let w__15 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let state_match ← (( do
        (AArch64_StateMatch (_get_DBGBCR_EL1_Type_SSC (GetElem?.getElem! w__13 n)) ssce
          (_get_DBGBCR_EL1_Type_HMC (GetElem?.getElem! w__14 n))
          (_get_DBGBCR_EL1_Type_PMC (GetElem?.getElem! w__15 n)) linked linked_n isbreakpnt vaddress
          accdesc) ) : SailM Bool )
      let w__16 ← (( do (AArch64_BreakpointValueMatch n vaddress linked_to isbreakpnt) ) : SailM
        (Bool × Bool) )
      let (tup__0, tup__1) := (w__16 : (Bool × Bool))
      let value_match_name : Bool := tup__0
      let valid_mismatch_name : Bool := tup__1
      let value_match_name ← (( do
        if (((HaveAArch32 ()) && (size == 4)) : Bool)
        then
          (do
            let (__tup_0, _) ← (( do
              (AArch64_BreakpointValueMatch n (BitVec.addInt vaddress 2) linked_to isbreakpnt) ) :
              SailM (Bool × Bool) )
            let match_i : Bool := __tup_0
            if (((! value_match_name) && match_i) : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
            else (pure (value_match_name)))
        else (pure (value_match_name)) ) : SailM Bool )
      let w__19 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress 1)])) == 1#1) : Bool) : Bool)
        then
          (do
            let w__18 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((((_get_DBGBCR_EL1_Type_BAS (GetElem?.getElem! w__18 n)) == 0b1111#4) : Bool))))
        else (pure false) ) : SailM Bool )
      let value_match_name ← (( do
        if (w__19 : Bool)
        then
          (do
            if (value_match_name : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
            else (pure (value_match_name)))
        else (pure (value_match_name)) ) : SailM Bool )
      let val_match : Bool := ((value_match_name && state_match) && enabled)
      let is_mismatch : Bool := ((valid_mismatch_name && state_match) && enabled)
      (pure ((val_match, is_mismatch))))


/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 64 -/
def AArch64_WatchpointMatch (n : Nat) (vaddress : (BitVec 64)) (size : Int) (accdesc : AccessDescriptor) : SailM Bool := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert (! w__1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23776.61-23776.62"
  let w__2 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23777.42-23777.43"
  let enabled ← (( do (IsWatchpointEnabled n) ) : SailM Bool )
  let w__3 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let linked : Bool := ((_get_DBGWCR_EL1_Type_WT (GetElem?.getElem! w__3 n)) == 1#1)
  let isbreakpnt : Bool := false
  let w__4 ← (( do (Havev8p9Debug ()) ) : SailM Bool )
  let lbnx ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
        (pure ((_get_DBGWCR_EL1_Type_LBNX (GetElem?.getElem! w__5 n)))))
    else (pure (0b00#2)) ) : SailM (BitVec 2) )
  let w__6 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let linked_n : Int :=
    (BitVec.toNat (lbnx +++ (_get_DBGWCR_EL1_Type_LBN (GetElem?.getElem! w__6 n))))
  let w__7 ← (( do (HaveRME ()) ) : SailM Bool )
  let ssce ← (( do
    if (w__7 : Bool)
    then
      (do
        let w__8 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
        (pure ((_get_DBGWCR_EL1_Type_SSCE (GetElem?.getElem! w__8 n)))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let w__9 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__10 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__11 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__12 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let state_match ← (( do
    (AArch64_StateMatch (_get_DBGWCR_EL1_Type_SSC (GetElem?.getElem! w__9 n)) ssce
      (_get_DBGWCR_EL1_Type_HMC (GetElem?.getElem! w__10 n))
      (_get_DBGWCR_EL1_Type_PAC (GetElem?.getElem! w__11 n)) linked linked_n isbreakpnt w__12
      accdesc) ) : SailM Bool )
  let ls_match ← (( do (undefined_bool_at (← occLabel 1401) ()) ) : SailM Bool )
  let w__13 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let ls_match : Bool :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb
      (_get_DBGWCR_EL1_Type_LSC (GetElem?.getElem! w__13 n)) 1 0)) with
    | 0b00 => false
    | 0b01 => accdesc.read
    | 0b10 => (accdesc.write || (BEq.beq accdesc.acctype AccessType_DC))
    | 0b11 => true
    | _ => ls_match
  let value_match_name : Bool := false
  let value_match_name ← (( do
    let loop_byte_lower : Nat := 0
    let loop_byte_upper : Int := (size -i 1)
    (do
      let mut loop_vars := value_match_name
      for byte in [loop_byte_lower:loop_byte_upper:1]i do
        let value_match_name := loop_vars
        loop_vars ← do
          if ((value_match_name : Bool) : Bool)
          then (pure true)
          else
            (do
              (AArch64_WatchpointByteMatch n (BitVec.addInt vaddress byte)))
      (pure loop_vars)) ) : SailM Bool )
  (pure ((((value_match_name && state_match) && ls_match) && enabled)))


/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 16 -/
def AArch32_BreakpointMatch (n : Nat) (vaddress : (BitVec 32)) (accdesc : AccessDescriptor) (size : Int) : SailM (Bool × Bool) := do
  let match_i ← (( do (undefined_bool_at (← occLabel 2659) ()) ) : SailM Bool )
  let mismatch_i ← (( do (undefined_bool_at (← occLabel 2660) ()) ) : SailM Bool )
  let value_match_name ← (( do (undefined_bool_at (← occLabel 2661) ()) ) : SailM Bool )
  let value_mismatch_name ← (( do (undefined_bool_at (← occLabel 2662) ()) ) : SailM Bool )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:40445.51-40445.52"
  let w__2 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:40446.42-40446.43"
  let w__3 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let enabled : Bool := ((_get_DBGBCR_Type_E w__3) == 1#1)
  let isbreakpnt : Bool := true
  let w__4 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let b__0 := (_get_DBGBCR_Type_BT w__4)
  let linked : Bool :=
    (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
    then true
    else false : Bool)
  let linked_to : Bool := false
  let w__5 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let linked_n : Int := (BitVec.toNat (_get_DBGBCR_Type_LBN w__5))
  let w__6 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let w__8 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
  let state_match ← (( do
    (AArch32_StateMatch (_get_DBGBCR_Type_SSC w__6) (_get_DBGBCR_Type_HMC w__7)
      (_get_DBGBCR_Type_PMC w__8) linked linked_n isbreakpnt accdesc) ) : SailM Bool )
  let w__9 ← (( do (AArch32_BreakpointValueMatch n vaddress linked_to) ) : SailM (Bool × Bool) )
  let (tup__0, tup__1) := (w__9 : (Bool × Bool))
  let value_match_name : Bool := tup__0
  let value_mismatch_name : Bool := tup__1
  let (value_match_name, value_mismatch_name) ← (( do
    if ((size == 4) : Bool)
    then
      (do
        let w__10 ← (( do (AArch32_BreakpointValueMatch n (BitVec.addInt vaddress 2) linked_to) )
          : SailM (Bool × Bool) )
        let (tup__0, tup__1) := (w__10 : (Bool × Bool))
        let match_i : Bool := tup__0
        let mismatch_i : Bool := tup__1
        let value_match_name ← (( do
          if (((! value_match_name) && match_i) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
          else (pure (value_match_name)) ) : SailM Bool )
        let value_mismatch_name ← (( do
          if ((value_mismatch_name && (! mismatch_i)) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_BPMISMATCHHALF))
          else (pure (value_mismatch_name)) ) : SailM Bool )
        (pure ((value_match_name, value_mismatch_name))))
    else (pure ((value_match_name, value_mismatch_name))) ) : SailM (Bool × Bool) )
  let w__14 ← (( do
    if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress 1)])) == 1#1) : Bool) : Bool)
    then
      (do
        let w__13 ← (( do (DBGBCR_read n) ) : SailM (BitVec 32) )
        (pure ((((_get_DBGBCR_Type_BAS w__13) == 0b1111#4) : Bool))))
    else (pure false) ) : SailM Bool )
  let (value_match_name, value_mismatch_name) ← (( do
    if (w__14 : Bool)
    then
      (do
        let value_match_name ← (( do
          if (value_match_name : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
          else (pure (value_match_name)) ) : SailM Bool )
        let value_mismatch_name ← (( do
          if ((! value_mismatch_name) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_BPMISMATCHHALF))
          else (pure (value_mismatch_name)) ) : SailM Bool )
        (pure ((value_match_name, value_mismatch_name))))
    else (pure ((value_match_name, value_mismatch_name))) ) : SailM (Bool × Bool) )
  let val_match : Bool := ((value_match_name && state_match) && enabled)
  let mismatch : Bool := ((value_mismatch_name && state_match) && enabled)
  (pure ((val_match, mismatch)))


/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 16 -/
def AArch32_WatchpointMatch (n : Nat) (vaddress : (BitVec 32)) (size : Int) (accdesc : AccessDescriptor) : SailM Bool := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:40722.51-40722.52"
  let w__2 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:40723.42-40723.43"
  let w__3 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let enabled : Bool := ((_get_DBGWCR_Type_E w__3) == 1#1)
  let w__4 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let linked : Bool := ((_get_DBGWCR_Type_WT w__4) == 1#1)
  let isbreakpnt : Bool := false
  let w__5 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let linked_n : Int := (BitVec.toNat (_get_DBGWCR_EL1_Type_LBN (GetElem?.getElem! w__5 n)))
  let w__6 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let w__8 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let state_match ← (( do
    (AArch32_StateMatch (_get_DBGWCR_Type_SSC w__6) (_get_DBGWCR_Type_HMC w__7)
      (_get_DBGWCR_Type_PAC w__8) linked linked_n isbreakpnt accdesc) ) : SailM Bool )
  let ls_match ← (( do (undefined_bool_at (← occLabel 2676) ()) ) : SailM Bool )
  let w__9 ← (( do (DBGWCR_read n) ) : SailM (BitVec 32) )
  let ls_match : Bool :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb (_get_DBGWCR_Type_LSC w__9) 1 0)) with
    | 0b00 => false
    | 0b01 => accdesc.read
    | 0b10 => (accdesc.write || (BEq.beq accdesc.acctype AccessType_DC))
    | 0b11 => true
    | _ => ls_match
  let value_match_name : Bool := false
  let value_match_name ← (( do
    let loop_byte_lower : Nat := 0
    let loop_byte_upper : Int := (size -i 1)
    (do
      let mut loop_vars := value_match_name
      for byte in [loop_byte_lower:loop_byte_upper:1]i do
        let value_match_name := loop_vars
        loop_vars ← do
          if ((value_match_name : Bool) : Bool)
          then (pure true)
          else
            (do
              (AArch32_WatchpointByteMatch n (BitVec.addInt vaddress byte)))
      (pure loop_vars)) ) : SailM Bool )
  (pure ((((value_match_name && state_match) && ls_match) && enabled)))


def ALUWritePC (address : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  if ((BEq.beq w__0 InstrSet_A32) : Bool)
  then
    (do
      (BXWritePC address BranchType_INDIR))
  else
    (do
      (BranchWritePC address BranchType_INDIR))


def LoadWritePC (address : (BitVec 32)) : SailM Unit := do
  (BXWritePC address BranchType_INDIR)


/-- Type quantifiers: k_cold : Bool -/
def TakeReset (cold : Bool) : SailM Unit := do
  ArmFull.assert (((HighestEL ()) == EL1) || (((HighestEL ()) == EL2) || ((HighestEL ()) == EL3))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:1400.71-1400.72"
  writeReg FEAT_DoubleLock_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  (InitVariantImplemented ())
  (InitFeatureImpl ())
  if (cold : Bool)
  then
    (do
      let w__0 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__0 15 12 CFG_ID_AA64PFR0_EL1_EL3)
      let w__1 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__1 11 8 CFG_ID_AA64PFR0_EL1_EL2)
      let w__2 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__2 7 4 CFG_ID_AA64PFR0_EL1_EL1)
      let w__3 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__3 3 0 CFG_ID_AA64PFR0_EL1_EL0)
      let w__4 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__4 1 1 1#1)
      let w__5 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      let w__6 ← (( do readReg CFG_RMR_AA64 ) : SailM (BitVec 1) )
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__5 0 0 w__6))
  else (pure (()))
  let w__7 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  if (((_get_RMR_EL3_Type_AA64 w__7) == 1#1) : Bool)
  then
    (do
      writeReg __highest_el_aarch32 false
      let w__8 ← (( do readReg CFG_RVBAR ) : SailM (BitVec 64) )
      (SetResetVector w__8)
      (AArch64_TakeReset cold))
  else
    (do
      let questionMark := (HighestEL ())
      if ((questionMark == EL3) : Bool)
      then
        (do
          let w__9 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
          ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL3 w__9) == 0b0010#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:1420.51-1420.52")
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__10 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
              ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL2 w__10) == 0b0010#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:1423.51-1423.52")
          else
            (do
              if ((questionMark == EL1) : Bool)
              then
                (do
                  let w__11 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
                  ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL1 w__11) == 0b0010#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:1426.51-1426.52")
              else (pure (()))))
      writeReg __highest_el_aarch32 true
      let w__12 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__12
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL0))) false)
      let w__13 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__13
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL1))) false)
      let w__14 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__14
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL2))) false)
      let w__15 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__15
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL3))) false)
      let w__16 ← (( do readReg __ignore_rvbar_in_aarch32 ) : SailM Bool )
      if (w__16 : Bool)
      then
        (do
          (SetResetVector (Sail.BitVec.zeroExtend 0x0#4 64)))
      else
        (do
          let w__17 ← (( do readReg CFG_RVBAR ) : SailM (BitVec 64) )
          (SetResetVector w__17))
      if ((HaveEL EL3) : Bool)
      then
        (do
          let w__18 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__18 0 0 0#1))
      else (pure (()))
      (AArch32_TakeReset cold))
  let w__19 ← (( do readReg ZCR_EL3_LEN_VALUE ) : SailM Int )
  if ((w__19 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__20 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
      let w__21 ← (( do readReg ZCR_EL3_LEN_VALUE ) : SailM Int )
      writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__20 3 0 (integer_subrange w__21 3 0)))
  else (pure (()))
  let w__22 ← (( do readReg CPTR_EL3_EZ_VALUE ) : SailM Int )
  if ((w__22 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__23 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      let w__24 ← (( do readReg CPTR_EL3_EZ_VALUE ) : SailM Int )
      writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__23 8 8
        (BitVec.setWidth 1 (BitVec.join1 [(integer_access w__24 0)]))))
  else (pure (()))
  let w__25 ← (( do readReg CPTR_EL3_ESM_VALUE ) : SailM Int )
  if ((w__25 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__26 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      let w__27 ← (( do readReg CPTR_EL3_ESM_VALUE ) : SailM Int )
      writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__26 12 12
        (BitVec.setWidth 1 (BitVec.join1 [(integer_access w__27 0)]))))
  else (pure (()))
  let w__28 ← (( do readReg SMCR_EL3_LEN_VALUE ) : SailM Int )
  if ((w__28 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__29 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
      let w__30 ← (( do readReg SMCR_EL3_LEN_VALUE ) : SailM Int )
      writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__29 3 0 (integer_subrange w__30 3 0)))
  else (pure (()))


def execute_aarch32_instrs_B_Op_A_txt (imm32 : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
  (BranchWritePC (w__0 + imm32) BranchType_DIR)


def execute_aarch32_instrs_BL_i_Op_A_txt (imm32 : (BitVec 32)) (targetInstrSet : InstrSet) : SailM Unit := do
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  if ((BEq.beq w__0 InstrSet_A32) : Bool)
  then
    (do
      let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      (LR_write (BitVec.subInt w__1 4)))
  else
    (do
      let w__2 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      (LR_write ((Sail.BitVec.extractLsb w__2 31 1) +++ 1#1)))
  let targetAddress ← (( do (undefined_bitvector_at (← occLabel 2981) 32) ) : SailM (BitVec 32)
    )
  let targetAddress ← (( do
    if ((BEq.beq targetInstrSet InstrSet_A32) : Bool)
    then
      (do
        let w__3 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        let targetAddress := (((Align_bits w__3 4) + imm32) : (BitVec 32))
        (pure (targetAddress)))
    else
      (do
        let w__4 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        let targetAddress := ((w__4 + imm32) : (BitVec 32))
        (pure (targetAddress))) ) : SailM (BitVec 32) )
  (SelectInstrSet targetInstrSet)
  (BranchWritePC targetAddress BranchType_DIRCALL)


/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BLX_r_Op_A_txt (m : Nat) : SailM Unit := do
  let target ← (( do (R_read m) ) : SailM (BitVec 32) )
  let next_instr_addr ← (( do (undefined_bitvector_at (← occLabel 2982) 32) ) : SailM
    (BitVec 32) )
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  if ((BEq.beq w__0 InstrSet_A32) : Bool)
  then
    (do
      let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      let next_instr_addr : (BitVec 32) := (BitVec.subInt w__1 4)
      (LR_write next_instr_addr))
  else
    (do
      let w__2 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      let next_instr_addr : (BitVec 32) := (BitVec.subInt w__2 2)
      (LR_write ((Sail.BitVec.extractLsb next_instr_addr 31 1) +++ 1#1)))
  (BXWritePC target BranchType_INDCALL)


end ArmFull.Functions
