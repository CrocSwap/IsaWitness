module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0008
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0037
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0066
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0165
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0185
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0216
public import ArmFull.Fn.M0218
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0241
public import ArmFull.Fn.M0242 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 64 -/
def AArch64_WatchpointMatch (n : Nat) (vaddress : (BitVec 64)) (size : Int) (accdesc : AccessDescriptor) : SailM Bool := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:23786.61-23786.62"
  let w__2 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "sail-inputs/03-v8_base.sail:23787.42-23787.43"
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
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:40455.51-40455.52"
  let w__2 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "sail-inputs/03-v8_base.sail:40456.42-40456.43"
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
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:40732.51-40732.52"
  let w__2 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "sail-inputs/03-v8_base.sail:40733.42-40733.43"
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
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
         (pure (((w__0 == EL1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
             (pure (((w__1 == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
            (pure (((w__2 == EL3) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/13-reset.sail:1400.71-1400.72"
  writeReg FEAT_DoubleLock_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  (InitVariantImplemented ())
  (InitFeatureImpl ())
  if (cold : Bool)
  then
    (do
      let w__5 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__5 15 12 CFG_ID_AA64PFR0_EL1_EL3)
      let w__6 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__6 11 8 CFG_ID_AA64PFR0_EL1_EL2)
      let w__7 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__7 7 4 CFG_ID_AA64PFR0_EL1_EL1)
      let w__8 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__8 3 0 CFG_ID_AA64PFR0_EL1_EL0)
      let w__9 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__9 1 1 1#1)
      let w__10 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      let w__11 ← (( do readReg CFG_RMR_AA64 ) : SailM (BitVec 1) )
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__10 0 0 w__11))
  else (pure (()))
  let w__12 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  if (((_get_RMR_EL3_Type_AA64 w__12) == 1#1) : Bool)
  then
    (do
      writeReg __highest_el_aarch32 false
      let w__13 ← (( do readReg CFG_RVBAR ) : SailM (BitVec 64) )
      (SetResetVector w__13)
      (AArch64_TakeReset cold))
  else
    (do
      let questionMark ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
      if ((questionMark == EL3) : Bool)
      then
        (do
          let w__14 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
          ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL3 w__14) == 0b0010#4) "sail-inputs/13-reset.sail:1420.51-1420.52")
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
              ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL2 w__15) == 0b0010#4) "sail-inputs/13-reset.sail:1423.51-1423.52")
          else
            (do
              if ((questionMark == EL1) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
                  ArmFull.assert ((_get_ID_AA64PFR0_EL1_Type_EL1 w__16) == 0b0010#4) "sail-inputs/13-reset.sail:1426.51-1426.52")
              else (pure (()))))
      writeReg __highest_el_aarch32 true
      let w__17 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__17
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL0))) false)
      let w__18 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__18
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL1))) false)
      let w__19 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__19
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL2))) false)
      let w__20 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
      writeReg FeatureImpl (vectorUpdate w__20
        (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL3))) false)
      let w__21 ← (( do readReg __ignore_rvbar_in_aarch32 ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          (SetResetVector (Sail.BitVec.zeroExtend 0x0#4 64)))
      else
        (do
          let w__22 ← (( do readReg CFG_RVBAR ) : SailM (BitVec 64) )
          (SetResetVector w__22))
      let w__23 ← (( do (HaveEL EL3) ) : SailM Bool )
      if (w__23 : Bool)
      then
        (do
          let w__24 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__24 0 0 0#1))
      else (pure (()))
      (AArch32_TakeReset cold))
  let w__25 ← (( do readReg ZCR_EL3_LEN_VALUE ) : SailM Int )
  if ((w__25 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__26 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
      let w__27 ← (( do readReg ZCR_EL3_LEN_VALUE ) : SailM Int )
      writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__26 3 0 (integer_subrange w__27 3 0)))
  else (pure (()))
  let w__28 ← (( do readReg CPTR_EL3_EZ_VALUE ) : SailM Int )
  if ((w__28 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__29 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      let w__30 ← (( do readReg CPTR_EL3_EZ_VALUE ) : SailM Int )
      writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__29 8 8
        (BitVec.setWidth 1 (BitVec.join1 [(integer_access w__30 0)]))))
  else (pure (()))
  let w__31 ← (( do readReg CPTR_EL3_ESM_VALUE ) : SailM Int )
  if ((w__31 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__32 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      let w__33 ← (( do readReg CPTR_EL3_ESM_VALUE ) : SailM Int )
      writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__32 12 12
        (BitVec.setWidth 1 (BitVec.join1 [(integer_access w__33 0)]))))
  else (pure (()))
  let w__34 ← (( do readReg SMCR_EL3_LEN_VALUE ) : SailM Int )
  if ((w__34 != (Neg.neg 1)) : Bool)
  then
    (do
      let w__35 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
      let w__36 ← (( do readReg SMCR_EL3_LEN_VALUE ) : SailM Int )
      writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__35 3 0 (integer_subrange w__36 3 0)))
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


/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BX_Op_A_txt (m : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  (BXWritePC w__0 BranchType_INDIR)


/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BXJ_Op_A_txt (m : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  (BXWritePC w__0 BranchType_INDIR)


/-- Type quantifiers: n : Nat, k_nonzero : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_CBNZ_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) (nonzero : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((neq_bool nonzero (IsZero w__0)) : Bool)
  then
    (do
      let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      (CBWritePC (w__1 + imm32)))
  else (pure (()))


/-- Type quantifiers: k_retry : Bool -/
def execute_aarch64_instrs_system_tme_tcancel (reason : (BitVec 15)) (retry : Bool) : SailM Unit := do
  let w__0 ← (( do (IsTMEEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do readReg TSTATE ) : SailM TMState )
  if ((w__1.depth >b 0) : Bool)
  then
    (do
      (FailTransaction__1 TMFailure_CNCL retry false reason))
  else (pure (()))


/-- Type quantifiers: k_is_async : Bool -/
def Halt__1 (reason : (BitVec 6)) (is_async : Bool) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_DBG false))
  else (pure (()))
  let _ : Unit := (CTI_SignalEvent CrossTriggerIn_CrossHalt)
  let preferred_restart_address ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let spsr ← (( do (GetPSRFromPSTATE DebugState 64) ) : SailM (BitVec 64) )
  let w__7 ← (( do
    if ((← do
         (pure ((← do
               (pure ((← do
                     (HaveBTIExt ())) && ((! is_async) : Bool)))) && ((! ((reason == DebugHalt_Step_Normal) || ((reason == DebugHalt_Step_Exclusive) || ((reason == DebugHalt_Step_NoSyndrome) || ((reason == DebugHalt_Breakpoint) || (reason == DebugHalt_HaltInstruction)))))) : Bool)))) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_ZEROBTYPE))
    else (pure false) ) : SailM Bool )
  let spsr : (BitVec 64) :=
    if (w__7 : Bool)
    then (Sail.BitVec.updateSubrange spsr 11 10 0b00#2)
    else spsr
  let w__8 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (DLR_write (Sail.BitVec.extractLsb preferred_restart_address 31 0))
      (DSPSR_write (Mk_DSPSR_Type (Sail.BitVec.extractLsb spsr 31 0)))
      let w__9 ← (( do (Havev8p9Debug ()) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (DSPSR2_write (Mk_DSPSR2_Type (Sail.BitVec.extractLsb spsr 63 32))))
      else (pure (())))
  else
    (do
      writeReg DLR_EL0 preferred_restart_address
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type spsr))
  let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ITE w__10 1#1))
  let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ITO w__11 0#1))
  let w__12 ← (( do (HaveRME ()) ) : SailM Bool )
  if (w__12 : Bool)
  then
    (do
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__13.EL == EL3) : Bool)
      then
        (do
          let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          (EDSCR_write (_update_EDSCR_Type_SDD w__14 0#1)))
      else
        (do
          let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          let w__16 ← (( do (ExternalRootInvasiveDebugEnabled ()) ) : SailM Bool )
          let w__17 : (BitVec 1) :=
            if (w__16 : Bool)
            then 0#1
            else 1#1
          (EDSCR_write (_update_EDSCR_Type_SDD w__15 w__17))))
  else
    (do
      let w__18 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      if ((BEq.beq w__18 SS_Secure) : Bool)
      then
        (do
          let w__19 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          (EDSCR_write (_update_EDSCR_Type_SDD w__19 0#1)))
      else
        (do
          let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
          if (w__20 : Bool)
          then
            (do
              let w__21 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
              let w__22 ← (( do (ExternalSecureInvasiveDebugEnabled ()) ) : SailM Bool )
              let w__23 : (BitVec 1) :=
                if (w__22 : Bool)
                then 0#1
                else 1#1
              (EDSCR_write (_update_EDSCR_Type_SDD w__21 w__23)))
          else
            (do
              let w__24 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
              (EDSCR_write (_update_EDSCR_Type_SDD w__24 1#1)))))
  let w__25 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_MA w__25 0#1))
  let w__26 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__26 : Bool)
  then
    (do
      let split_vec ← (( do (__UNKNOWN_bits 14) ) : SailM (BitVec 14) )
      let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__27 with IT := (Sail.BitVec.extractLsb split_vec 13 6) }
      let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__28 with SS := (Sail.BitVec.extractLsb split_vec 5 5) }
      let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__29 with SSBS := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__30 with A := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__31 with I := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__32 with F := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__33 with T := (Sail.BitVec.extractLsb split_vec 0 0) })
  else
    (do
      let split_vec ← (( do (__UNKNOWN_bits 6) ) : SailM (BitVec 6) )
      let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__34 with SS := (Sail.BitVec.extractLsb split_vec 5 5) }
      let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__35 with SSBS := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__36 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__37 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__37 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__38 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__39 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__39 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__40 with TCO := 1#1 }
      let w__41 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__41 with BTYPE := 0b00#2 })
  let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__42 with IL := 0#1 }
  let _ : Unit := (StopInstructionPrefetchAndEnableITR ())
  let w__43 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_STATUS w__43 reason))
  (UpdateEDSCRFields ())
  if ((! is_async) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))


def AArch64_TakeExceptionInDebugState (target_el : (BitVec 2)) (exception_in : ExceptionRecord) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveEL target_el)) : Bool)
         then
           (do
             let w__1 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__3.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:9870.105-9870.106"
  let w__6 ← (( do
    if (((target_el != EL3) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_EDSCR_Type_SDD w__5) == 0#1) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__6 "sail-inputs/03-v8_base.sail:9871.54-9871.55"
  let except : ExceptionRecord := exception_in
  let sync_errors ← (( do (undefined_bool_at (← occLabel 693) ()) ) : SailM Bool )
  let w__7 ← (( do (HaveIESB ()) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__7 : Bool)
    then
      (do
        let w__8 ← (( do (SCTLR_read target_el) ) : SailM (BitVec 64) )
        let sync_errors := (((_get_SCTLRType_IESB w__8) == 1#1) : Bool)
        let w__9 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
        let sync_errors ← (( do
          if (w__9 : Bool)
          then
            (do
              if ((sync_errors : Bool) : Bool)
              then (pure true)
              else
                (do
                  (pure ((← do
                        let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        let w__11 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure (((((_get_SCR_EL3_Type_EA w__10) +++ (_get_SCR_EL3_Type_NMEA w__11)) == 0b11#2) : Bool)))) && ((target_el == EL3) : Bool)))))
          else (pure (sync_errors)) ) : SailM Bool )
        let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
        let sync_errors : Bool :=
          if ((! w__14) : Bool)
          then false
          else sync_errors
        (pure (sync_errors)))
    else (pure (false)) ) : SailM Bool )
  let w__17 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__16 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__16.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      let cause ← (( do (undefined_TMFailure (← occLabel 694) ()) ) : SailM TMFailure )
      let cause : TMFailure :=
        match except.exceptype with
        | .Exception_SoftwareBreakpoint => TMFailure_DBG
        | .Exception_Breakpoint => TMFailure_DBG
        | .Exception_Watchpoint => TMFailure_DBG
        | .Exception_SoftwareStep => TMFailure_DBG
        | _ => TMFailure_ERR
      let cause := cause
      (FailTransaction cause false))
  else (pure (()))
  let _ : Unit := (SynchronizeContext ())
  let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (from_32 : Bool)
  then
    (do
      (AArch64_MaybeZeroRegisterUppers ()))
  else (pure (()))
  let w__21 ← (( do
    if ((← if (from_32 : Bool)
         then
           (do
             (HaveSME ()))
         else (pure false)) : Bool)
    then
      (do
        let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__20.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__21 : Bool)
  then
    (do
      (ResetSVEState ()))
  else
    (do
      (MaybeZeroSVEUppers target_el))
  (AArch64_ReportException except target_el)
  let w__22 ← (( do (HaveGCS ()) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__23 with EXLOCK := 0#1 })
  else (pure (()))
  let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__24 with EL := target_el }
  let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__25 with nRW := 0#1 }
  let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__26 with SP := 1#1 }
  let w__27 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (SPSR_set (N := 64) w__27)
  let w__28 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (ELR_set__1 w__28)
  let split_vec ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
  let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__29 with SS := (Sail.BitVec.extractLsb split_vec 4 4) }
  let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__30 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__31 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__32 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__33 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__34 with IL := 0#1 }
  if (from_32 : Bool)
  then
    (do
      let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__35 with IT := 0b00000000#8 }
      let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__36 with T := 0#1 })
  else (pure (()))
  let w__45 ← (( do
    if ((← do
         if ((← do
              (HavePANExt ())) : Bool)
         then
           (do
             if ((← do
                  let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__38.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      let w__39 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__39.EL == EL2) : Bool)))) : Bool)
                 then
                   (do
                     (ELIsInHost EL0))
                 else (pure false)))
         else (pure false)) : Bool)
    then
      (do
        let w__44 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_SPAN w__44) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__45 : Bool)
  then
    (do
      let w__46 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__46 with PAN := 1#1 })
  else (pure (()))
  let w__47 ← (( do (HaveUAOExt ()) ) : SailM Bool )
  if (w__47 : Bool)
  then
    (do
      let w__48 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__48 with UAO := 0#1 })
  else (pure (()))
  let w__49 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if (w__49 : Bool)
  then
    (do
      let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__50 with BTYPE := 0b00#2 }
      writeReg BTypeNext 0b00#2)
  else (pure (()))
  let w__51 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
  if (w__51 : Bool)
  then
    (do
      let w__52 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__53 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
      writeReg PSTATE { w__52 with SSBS := w__53 })
  else (pure (()))
  let w__54 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if (w__54 : Bool)
  then
    (do
      let w__55 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__55 with TCO := 1#1 })
  else (pure (()))
  let w__56 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DLR_EL0 w__56
  let w__57 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__57)
  let w__58 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ERR w__58 1#1))
  (UpdateEDSCRFields ())
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (EndOfInstruction ())


end ArmFull.Functions
