module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0108
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0180
public import ArmFull.Fn.M0181 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_GenerateDebugExceptionsFrom (from_el : (BitVec 2)) (from_state : SecurityState) (mask : (BitVec 1)) : SailM Bool := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_OSLSR_EL1_Type_OSLK w__0) == 1#1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             (DoubleLockStatus ()))) : Bool)
    then (pure true)
    else
      (do
        (Halted ())) ) : SailM Bool )
  if (w__4 : Bool)
  then (pure (false))
  else
    (do
      let route_to_el2 ← (( do
        if ((← do
             if ((← do
                  (HaveEL EL2)) : Bool)
             then
               (do
                 if (((bne from_state SS_Secure) : Bool) : Bool)
                 then (pure true)
                 else
                   (do
                     (IsSecureEL2Enabled ())))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_TGE w__9) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_TDE w__10) == 1#1) : Bool)))))
        else (pure false) ) : SailM Bool )
      let target : (BitVec 2) :=
        if (route_to_el2 : Bool)
        then EL2
        else EL1
      let enabled ← (( do (undefined_bool_at (← occLabel 647) ()) ) : SailM Bool )
      let w__13 ← (( do
        (pure ((← do
              (HaveEL EL3)) && ((BEq.beq from_state SS_Secure) : Bool))) ) : SailM Bool )
      let enabled ← (( do
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
            let enabled := (((_get_MDCR_EL3_Type_SDD w__14) == 0#1) : Bool)
            let w__16 ← (( do
              if (((from_el == EL0) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL1))
              else (pure false) ) : SailM Bool )
            if (w__16 : Bool)
            then
              (do
                if ((enabled : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__17 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
                    (pure ((((_get_SDER32_EL3_Type_SUIDEN w__17) == 1#1) : Bool)))))
            else (pure (enabled)))
        else (pure (true)) ) : SailM Bool )
      if ((from_el == target) : Bool)
      then
        (do
          (pure ((← do
                if ((enabled : Bool) : Bool)
                then
                  (do
                    let w__19 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
                    (pure ((((_get_MDSCR_EL1_Type_KDE w__19) == 1#1) : Bool))))
                else (pure false)) && ((mask == 0#1) : Bool))))
      else
        (let enabled : Bool :=
          (enabled && (((BitVec.toNat target) >b (BitVec.toNat from_el)) : Bool))
        (pure (enabled))))


/-- Type quantifiers: k_ex10380618_ : Bool -/
def C27bConstrainControl (isbreakpnt : Bool) : SailM (Constraint × (BitVec 6)) := do
  let disabled ← (( do (undefined_bool_at (← occLabel 1378) ()) ) : SailM Bool )
  if (disabled : Bool)
  then
    (do
      let w__0 ← (( do (undefined_bitvector_at (← occLabel 1379) 6) ) : SailM (BitVec 6) )
      (pure ((Constraint_DISABLED, (w__0 : (BitVec 6))))))
  else
    (do
      let allowed : (BitVec 256) := (Zeros (n := 256))
      let allowed ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Nat := 63
        (do
          let mut loop_vars := allowed
          for i in [loop_i_lower:loop_i_upper:1]i do
            let allowed := loop_vars
            loop_vars ← do
              let raw : (BitVec 6) := (integer_subrange i 5 0)
              let w__1 ← (( do
                (C27bReservedControl (Sail.BitVec.extractLsb raw 4 3)
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access raw 2)]))
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access raw 5)]))
                  (Sail.BitVec.extractLsb raw 1 0) isbreakpnt) ) : SailM Bool )
              let allowed : (BitVec 256) :=
                if ((! w__1) : Bool)
                then (BitVec.update allowed (Sail.Int.toNatChecked (i)) 1#1)
                else allowed
              (pure (allowed))
          (pure loop_vars)) ) : SailM (BitVec 256) )
      let selected ← (( do (C27bSelect allowed) ) : SailM Int )
      (pure ((Constraint_UNKNOWN, (integer_subrange selected 5 0)))))


/-- Type quantifiers: n : Int -/
def IsContextMatchingBreakpoint (n : Int) : SailM Bool := do
  let lower ← (( do (undefined_int_at (← occLabel 1381) ()) ) : SailM Int )
  let upper ← (( do (undefined_int_at (← occLabel 1382) ()) ) : SailM Int )
  let w__0 ← (( do (ContextMatchingBreakpointRange ()) ) : SailM (Int × Int) )
  let (tup__0, tup__1) := (w__0 : (Int × Int))
  let lower : Int := tup__0
  let upper : Int := tup__1
  let upper : Int := upper
  let lower : Int := lower
  (pure (((n ≥b lower) && (n ≤b upper))))


/-- Type quantifiers: k_N : Nat, level : Int, 0 < k_N -/
def AArch64_DecodeDescriptorType (descriptor : (BitVec k_N)) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (level : Int) : SailM DescriptorType := do
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 0)])) == 0#1) : Bool)
  then (pure (DescriptorType_Invalid))
  else
    (do
      if ((d128 == 1#1) : Bool)
      then
        (do
          ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:24914.35-24914.36"
          let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
          (pure (if ((((BEq.beq tgx TGx_16KB) || (BEq.beq tgx TGx_64KB)) && (((BitVec.toNat skl) == 3) : Bool)) : Bool)
            then DescriptorType_Invalid
            else
              (let effective_level : Int := (level +i (BitVec.toNat skl))
              if ((effective_level >b FINAL_LEVEL) : Bool)
              then DescriptorType_Invalid
              else
                (if ((effective_level == FINAL_LEVEL) : Bool)
                then DescriptorType_Leaf
                else DescriptorType_Table)))))
      else
        (do
          ArmFull.assert (1 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:24928.33-24928.34"
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 1)])) == 1#1) : Bool)
          then
            (pure (if ((level == FINAL_LEVEL) : Bool)
              then DescriptorType_Leaf
              else DescriptorType_Table))
          else
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 1)])) == 0#1) : Bool)
              then
                (do
                  let w__0 ← (( do (AArch64_BlockDescSupported d128 ds tgx level) ) : SailM Bool )
                  let w__1 : DescriptorType :=
                    if (w__0 : Bool)
                    then DescriptorType_Leaf
                    else DescriptorType_Invalid
                  (pure (w__1)))
              else
                (do
                  (undefined_DescriptorType (← occLabel 1471) ())))))


def AArch64_OAOutOfRange (address : (BitVec 56)) (d128 : (BitVec 1)) (ps : (BitVec 3)) (tgx : TGx) : SailM Bool := do
  let oasize ← (( do (AArch64_PhysicalAddressSize d128 ps tgx) ) : SailM Int )
  (pure (if ((oasize <b 56) : Bool)
    then (! (is_zero_subrange address 55 oasize))
    else false))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_S2TxSZFaults (walkparams : S2TTWParams) (s1aarch64 : Bool) : SailM Bool := do
  let mintxsz ← (( do (AArch64_S2MinTxSZ walkparams.d128 walkparams.ds walkparams.tgx s1aarch64) )
    : SailM Int )
  let maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailM Int )
  if (((BitVec.toNat walkparams.txsz) <b mintxsz) : Bool)
  then
    (do
      if ((← do
           (Have52BitPAExt ())) : Bool)
      then (pure true)
      else
        (do
          (__IMPDEF_boolean "Fault on TxSZ value below minimum")))
  else
    (do
      if (((BitVec.toNat walkparams.txsz) >b maxtxsz) : Bool)
      then
        (do
          (__IMPDEF_boolean "Fault on TxSZ value above maximum"))
      else (pure (false)))


/-- Type quantifiers: idx : Nat, increment_name : Int, 0 ≤ idx ∧ idx < 31 -/
def AArch64_IncrementEventCounter (idx : Nat) (increment_name : Int) : SailM Unit := do
  let ovflw : Int := 32
  let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let old_value : Int := (BitVec.toNat (GetElem?.getElem! w__0 idx))
  let w__1 ← (( do (PMUCountValue idx increment_name) ) : SailM Int )
  let new_value : Int := (old_value +i w__1)
  let lp ← (( do (undefined_bitvector_at (← occLabel 2422) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
  let (lp, ovflw) ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__3 idx (integer_subrange new_value 63 0))
        let w__4 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
        let w__7 ← (( do
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HLP w__5))))
          else
            (do
              let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_LP w__6)))) ) : SailM (BitVec 1) )
        let lp := (w__7 : (BitVec 1))
        let ovflw : Int :=
          if ((lp == 1#1) : Bool)
          then 64
          else 32
        (pure ((lp, ovflw))))
    else
      (do
        let w__8 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
        writeReg PMEVCNTR_EL0 (vectorUpdate w__8 idx
          (Sail.BitVec.zeroExtend (integer_subrange new_value 31 0) 64))
        let ovflw : Int := 32
        (pure ((lp, ovflw)))) ) : SailM ((BitVec 1) × Int) )
  let ovflw : Int := ovflw
  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
         old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
  then
    (do
      let w__9 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSSET_EL0 (BitVec.update w__9 idx (Bit 1#1))
      let w__10 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
      writeReg PMOVSCLR_EL0 (BitVec.update w__10 idx (Bit 1#1))
      let w__15 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(integer_access idx 0)])) == 0#1) : Bool) : Bool)
             then
               (do
                 let w__11 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                 (pure ((((idx +i 1) <b w__11) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (pure ((← do
                  let w__13 ← (( do (HavePMUv3p5 ()) ) : SailM Bool )
                  (pure (((! w__13) : Bool)))) || ((lp == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (PMUEvent__2 PMU_EVENT_CHAIN 1 (idx +i 1)))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV94 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap4_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV93 enabled)
      (__ConfigureV89 enabled))
  else (pure (()))


def AArch32_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int_at (← occLabel 500) ()) ) : SailM Int )
  let total_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        let w__8 ← (( do
          if ((! w__5) : Bool)
          then
            (do
              let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HPMN w__6))))
          else
            (do
              let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_HDCR_Type_HPMN w__7)))) ) : SailM (BitVec 5) )
        let n : Int := ((BitVec.toNat w__8) : Int)
        let w__11 ← (( do
          if (((n >b total_counters) : Bool) : Bool)
          then (pure true)
          else
            (do
              (pure ((← do
                    let w__9 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                    (pure (((! w__9) : Bool)))) && ((n == 0) : Bool)))) ) : SailM Bool )
        if (w__11 : Bool)
        then
          (do
            let (_, __tup_1) ← (( do
              (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER) ) :
              SailM (Constraint × Int) )
            (pure (__tup_1)))
        else (pure (n)))
    else (pure (total_counters)) ) : SailM Int )
  let n : Int := n
  (pure (n))


def AArch64_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int_at (← occLabel 501) ()) ) : SailM Int )
  let total_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_MDCR_EL2_Type_HPMN w__5)) : Int)
        let w__8 ← (( do
          if (((n >b total_counters) : Bool) : Bool)
          then (pure true)
          else
            (do
              (pure ((← do
                    let w__6 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                    (pure (((! w__6) : Bool)))) && ((n == 0) : Bool)))) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let (_, __tup_1) ← (( do
              (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER) ) :
              SailM (Constraint × Int) )
            (pure (__tup_1)))
        else (pure (n)))
    else (pure (total_counters)) ) : SailM Int )
  let n : Int := n
  (pure (n))


def SecurityStateAtEL (EL : (BitVec 2)) : SailM SecurityState := SailME.run do
  let effective_nse_ns ← (( do (undefined_bitvector_at (← occLabel 503) 2) ) : SailME
    SecurityState (BitVec 2) )
  let w__0 ← (( do (HaveRME ()) ) : SailME SecurityState Bool )
  if (w__0 : Bool)
  then
    (do
      if ((EL == EL3) : Bool)
      then
        (do
          SailME.throw (SS_Root : SecurityState))
      else
        (do
          let w__1 ← (( do readReg SCR_EL3 ) : SailME SecurityState (BitVec 64) )
          let w__2 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailME SecurityState (BitVec 1) )
          let effective_nse_ns : (BitVec 2) := ((_get_SCR_EL3_Type_NSE w__1) +++ w__2)
          match effective_nse_ns with
          | 0b00 =>
            (do
              let w__3 ← (( do (HaveSecureEL2Ext ()) ) : SailME SecurityState Bool )
              if (w__3 : Bool)
              then
                (do
                  SailME.throw (SS_Secure : SecurityState))
              else
                (do
                  (Unreachable ())))
          | 0b01 =>
            (do
              SailME.throw (SS_NonSecure : SecurityState))
          | 0b11 =>
            (do
              SailME.throw (SS_Realm : SecurityState))
          | _ =>
            (do
              (Unreachable ()))))
  else (pure (()))
  let w__4 ← (( do (HaveEL EL3) ) : SailME SecurityState Bool )
  if ((! w__4) : Bool)
  then
    (do
      let w__5 ← (( do (SecureOnlyImplementation ()) ) : SailME SecurityState Bool )
      let w__6 : SecurityState :=
        if (w__5 : Bool)
        then SS_Secure
        else SS_NonSecure
      (pure (w__6)))
  else
    (do
      if ((EL == EL3) : Bool)
      then (pure (SS_Secure))
      else
        (do
          let w__8 ← (( do
            if (((EL != EL2) : Bool) : Bool)
            then (pure true)
            else
              (do
                (EL2Enabled ())) ) : SailME SecurityState Bool )
          ArmFull.assert w__8 "sail-inputs/03-v8_base.sail:4136.39-4136.40"
          let w__9 ← (( do (ELUsingAArch32 EL3) ) : SailME SecurityState Bool )
          if ((! w__9) : Bool)
          then
            (do
              let w__10 ← (( do readReg SCR_EL3 ) : SailME SecurityState (BitVec 64) )
              let w__11 : SecurityState :=
                if (((_get_SCR_EL3_Type_NS w__10) == 1#1) : Bool)
                then SS_NonSecure
                else SS_Secure
              (pure (w__11)))
          else
            (do
              let w__12 ← (( do readReg SCR ) : SailME SecurityState (BitVec 32) )
              let w__13 : SecurityState :=
                if (((_get_SCR_Type_NS w__12) == 1#1) : Bool)
                then SS_NonSecure
                else SS_Secure
              (pure (w__13)))))


/-- Type quantifiers: k_resvd_for_el2 : Bool -/
def HiLoPMUOverflow (resvd_for_el2 : Bool) : SailM Bool := do
  let check_cnten : Bool := false
  let check_e : Bool := false
  let check_inten : Bool := false
  let include_lo_name : Bool := (! resvd_for_el2)
  let include_hi_name : Bool := resvd_for_el2
  let exclude_cyc : Bool := false
  let exclude_sync : Bool := false
  (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name exclude_cyc
    exclude_sync)


def ELIsInHost (el : (BitVec 2)) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (ELUsingAArch32 EL2)) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let questionMark := el
      if ((questionMark == EL3) : Bool)
      then (pure (false))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__4) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((questionMark == EL1) : Bool)
              then (pure (false))
              else
                (do
                  if ((questionMark == EL0) : Bool)
                  then
                    (do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool))))
                      else (pure false))
                  else
                    (do
                      (Unreachable ())
                      (undefined_bool_at (← occLabel 563) ()))))))


def ProfilingBufferEnabled (_ : Unit) : SailM Bool := do
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 586) 2) ) : SailM (BitVec 2) )
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 587) ()) ) : SailM SecurityState )
  let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
      let (tup__0, tup__1) := (w__1 : (SecurityState × (BitVec 2)))
      let owning_ss : SecurityState := tup__0
      let owning_el : (BitVec 2) := tup__1
      let state_bits ← (( do (undefined_bitvector_at (← occLabel 588) 2) ) : SailM (BitVec 2) )
      let w__2 ← (( do (HaveRME ()) ) : SailM Bool )
      let state_bits ← (( do
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__4 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
            let state_bits := (((_get_SCR_EL3_Type_NSE w__3) +++ w__4) : (BitVec 2))
            (pure (state_bits)))
        else
          (do
            let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let state_bits := ((0#1 +++ (_get_SCR_EL3_Type_NS w__5)) : (BitVec 2))
            (pure (state_bits))) ) : SailM (BitVec 2) )
      let state_match ← (( do (undefined_bool_at (← occLabel 589) ()) ) : SailM Bool )
      let state_match : Bool :=
        match owning_ss with
        | .SS_Secure => (state_bits == 0b00#2)
        | .SS_NonSecure => (state_bits == 0b01#2)
        | .SS_Realm => (state_bits == 0b11#2)
        | _ => state_match
      if ((← do
           if ((← do
                (pure ((← do
                      let w__6 ← (( do (ELUsingAArch32 owning_el) ) : SailM Bool )
                      (pure (((! w__6) : Bool)))) && (state_match : Bool)))) : Bool)
           then
             (do
               let w__8 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
               (pure ((((_get_PMBLIMITR_EL1_Type_E w__8) == 1#1) : Bool))))
           else (pure false)) : Bool)
      then
        (do
          let w__10 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_PMBSR_EL1_Type_S w__10) == 0#1) : Bool))))
      else (pure false))


/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def ELFromSPSR (spsr : (BitVec k_N)) : SailM (Bool × (BitVec 2)) := do
  let el ← (( do (undefined_bitvector_at (← occLabel 631) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 632) ()) ) : SailM Bool )
  let effective_nse_ns ← (( do (undefined_bitvector_at (← occLabel 633) 2) ) : SailM (BitVec 2)
    )
  let (el, valid_name) ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 0#1) : Bool)
    then
      (do
        let el : (BitVec 2) := (Sail.BitVec.extractLsb spsr 3 2)
        let w__0 ← (( do (EffectiveSCR_EL3_NSE ()) ) : SailM (BitVec 1) )
        let w__1 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
        let effective_nse_ns : (BitVec 2) := (w__0 +++ w__1)
        let w__2 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let valid_name ← (( do
          if ((! w__2) : Bool)
          then (pure (false))
          else
            (do
              let w__3 ← (( do (HaveEL el) ) : SailM Bool )
              if ((! w__3) : Bool)
              then (pure (false))
              else
                (do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 1)])) == 1#1) : Bool)
                  then (pure (false))
                  else
                    (do
                      if (((el == EL0) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 0)])) == 1#1)) : Bool)
                      then (pure (false))
                      else
                        (do
                          let w__6 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveRME ())) && ((el != EL3) : Bool)))) && ((effective_nse_ns == 0b10#2) : Bool)))
                            ) : SailM Bool )
                          if (w__6 : Bool)
                          then (pure (false))
                          else
                            (do
                              let w__12 ← (( do
                                if ((← do
                                     if ((← do
                                          if (((el == EL2) : Bool) : Bool)
                                          then
                                            (do
                                              (HaveEL EL3))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__9 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
                                         (pure (((! w__9) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__11 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure ((((_get_SCR_EL3_Type_NS w__11) == 0#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              let valid_name : Bool :=
                                if (w__12 : Bool)
                                then false
                                else true
                              (pure (valid_name))))))) ) : SailM Bool )
        (pure ((el, valid_name))))
    else
      (do
        let w__13 ← (( do (HaveAArch32 ()) ) : SailM Bool )
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do (ELFromM32 (Sail.BitVec.extractLsb spsr 4 0)) ) : SailM
              (Bool × (BitVec 2)) )
            let (tup__0, tup__1) := (w__14 : (Bool × (BitVec 2)))
            let valid_name : Bool := tup__0
            let el : (BitVec 2) := tup__1
            (pure ((el, valid_name))))
        else
          (let valid_name : Bool := false
          (pure ((el, valid_name))))) ) : SailM ((BitVec 2) × Bool) )
  let el ← (( do
    if ((! valid_name) : Bool)
    then
      (do
        (__UNKNOWN_bits 2))
    else (pure (el)) ) : SailM (BitVec 2) )
  let el := el
  (pure ((valid_name, el)))


end ArmFull.Functions
