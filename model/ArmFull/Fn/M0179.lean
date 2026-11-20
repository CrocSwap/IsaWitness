module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0012
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178 set_option backward.proofsInPublic true @[expose] public section

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

def IsSecureEL2Enabled (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        (HaveSecureEL2Ext ()))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (HaveEL EL3) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__6 ← (( do
            if ((← do
                 let w__4 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                 (pure (((! w__4) : Bool)))) : Bool)
            then
              (do
                let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_SCR_EL3_Type_EEL2 w__5) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let w__7 : Bool :=
            if (w__6 : Bool)
            then true
            else false
          (pure (w__7)))
      else
        (do
          (SecureOnlyImplementation ())))
  else (pure (false))


def EffectiveSCR_EL3_NS (_ : Unit) : SailM (BitVec 1) := do
  let w__0 ← (( do (HaveSecureState ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (1#1))
  else
    (do
      let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
      if ((! w__1) : Bool)
      then (pure (0#1))
      else
        (do
          let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
          (pure ((_get_SCR_EL3_Type_NS w__2)))))


def ExternalSecureNoninvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (SecureOnlyImplementation ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do (HaveNoninvasiveDebugAuth ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          if ((← do
               (ExternalNoninvasiveDebugEnabled ())) : Bool)
          then
            (do
              if ((← do
                   let w__5 ← (( do readReg SPIDEN ) : SailM Signal )
                   (pure (((BEq.beq w__5 Signal_High) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__6 ← (( do readReg SPNIDEN ) : SailM Signal )
                  (pure (((BEq.beq w__6 Signal_High) : Bool)))))
          else (pure false))
      else
        (do
          (ExternalSecureInvasiveDebugEnabled ())))


/-- Type quantifiers: n : Int -/
def PMUCounterIsHyp (n : Int) : SailM Bool := do
  if ((n == INSTRUCTION_COUNTER_ID) : Bool)
  then (pure (false))
  else
    (do
      if ((n == CYCLE_COUNTER_ID) : Bool)
      then (pure (false))
      else
        (do
          let resvd_for_el2 ← (( do (undefined_bool_at (← occLabel 515) ()) ) : SailM Bool )
          let w__0 ← (( do (HaveEL EL2) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              let hpmn_bits ← (( do
                if (w__1 : Bool)
                then
                  (do
                    let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL2_Type_HPMN w__2))))
                else
                  (do
                    let w__3 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_HDCR_Type_HPMN w__3)))) ) : SailM (BitVec 5) )
              let resvd_for_el2 : Bool := (n ≥b (BitVec.toNat hpmn_bits))
              let w__7 ← (( do
                if ((← do
                     let w__4 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                     (pure ((((BitVec.toNat hpmn_bits) >b w__4) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__5 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                          (pure (((! w__5) : Bool)))) && ((IsZero hpmn_bits) : Bool)))) ) : SailM
                Bool )
              if (w__7 : Bool)
              then
                (do
                  (ConstrainUnpredictableBool Unpredictable_CounterReservedForEL2))
              else (pure (resvd_for_el2)))
          else (pure (false))))


def ExternalRootInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           if ((← do
                if ((← do
                     (ExternalInvasiveDebugEnabled ())) : Bool)
                then
                  (do
                    if ((← do
                         let w__2 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                         (pure (((! w__2) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        (ExternalSecureInvasiveDebugEnabled ())))
                else (pure false)) : Bool)
           then
             (do
               (ExternalRealmInvasiveDebugEnabled ()))
           else (pure false)) : Bool)
      then
        (do
          let w__8 ← (( do readReg RTPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__8 Signal_High) : Bool))))
      else (pure false))


def UpdateBranchRecordBuffer (ccu : (BitVec 1)) (cc : (BitVec 14)) (lastfailed : (BitVec 1)) (transactional : (BitVec 1)) (branch_type : (BitVec 6)) (el : (BitVec 2)) (mispredict : (BitVec 1)) (valid_name : (BitVec 2)) (source_address : (BitVec 64)) (target_address : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do (GetBRBENumRecords ()) ) : SailM Int )
  let loop_i_lower : Nat := 1
  let loop_i_upper : Int := (w__0 -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert (i <b 64) "sail-inputs/03-v8_base.sail:6440.39-6440.40"
        let w__1 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        let w__2 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_SRC (vectorUpdate w__1 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__2 (Sail.Int.toNatChecked ((i -i 1)))))
        let w__3 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        let w__4 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_TGT (vectorUpdate w__3 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__4 (Sail.Int.toNatChecked ((i -i 1)))))
        let w__5 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        let w__6 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_INF (vectorUpdate w__5 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__6 (Sail.Int.toNatChecked ((i -i 1)))))
    (pure loop_vars))
  let w__7 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__8 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__7 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__8 0) 46 46 ccu))
  let w__9 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__10 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__9 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__10 0) 45 32 cc))
  let w__11 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__12 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__11 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__12 0) 7 6 el))
  let w__13 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__14 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__13 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__14 0) 1 0 valid_name))
  let w__15 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__16 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__15 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__16 0) 16 16 transactional))
  let w__17 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__18 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__17 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__18 0) 17 17 lastfailed))
  let w__19 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__20 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__19 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__20 0) 5 5 mispredict))
  let w__21 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__22 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__21 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__22 0) 13 8 branch_type))
  let w__23 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_SRC (vectorUpdate w__23 0 (Mk_BRBSRCType source_address))
  let w__24 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_TGT (vectorUpdate w__24 0 (Mk_BRBTGTType target_address))


def DoubleLockStatus (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveDoubleLock ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          if ((← do
               if ((← do
                    let w__2 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                    (pure ((((_get_DBGOSDLR_Type_DLK w__2) == 1#1) : Bool)))) : Bool)
               then
                 (do
                   let w__3 ← (( do (DBGPRCR_read ()) ) : SailM (BitVec 32) )
                   (pure ((((_get_DBGPRCR_Type_CORENPDRQ w__3) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (Halted ()) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false))
      else
        (do
          if ((← do
               if ((← do
                    let w__7 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
                    (pure ((((_get_OSDLR_EL1_Type_DLK w__7) == 1#1) : Bool)))) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
                   (pure ((((_get_DBGPRCR_EL1_Type_CORENPDRQ w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__10 ← (( do (Halted ()) ) : SailM Bool )
              (pure (((! w__10) : Bool))))
          else (pure false)))


def DebugTargetFrom (from_state : SecurityState) : SailM (BitVec 2) := do
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 650) ()) ) : SailM Bool )
  let w__7 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        if (((bne from_state SS_Secure) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (HaveSecureEL2Ext ())) : Bool)
            then
              (do
                if ((← do
                     let w__2 ← (( do (HaveEL EL3) ) : SailM Bool )
                     (pure (((! w__2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_EEL2 w__3) == 1#1) : Bool)))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__7 : Bool)
    then
      (do
        let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            if ((← do
                 let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((_get_HDCR_Type_TDE w__9) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__10 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_TGE w__10) == 1#1) : Bool)))))
        else
          (do
            if ((← do
                 let w__12 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_MDCR_EL2_Type_TDE w__12) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__13) == 1#1) : Bool))))))
    else (pure (false)) ) : SailM Bool )
  let target ← (( do (undefined_bitvector_at (← occLabel 651) 2) ) : SailM (BitVec 2) )
  if (route_to_el2 : Bool)
  then (pure (EL2))
  else
    (do
      let w__18 ← (( do
        (pure ((← do
              if ((← do
                   (HaveEL EL3)) : Bool)
              then
                (do
                  let w__16 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  (pure (((! w__16) : Bool))))
              else (pure false)) && ((BEq.beq from_state SS_Secure) : Bool))) ) : SailM Bool )
      let target : (BitVec 2) :=
        if (w__18 : Bool)
        then EL3
        else EL1
      (pure (target)))


def IsVirtualSErrorPending (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (pure (((_get_HCR_Type_VA w__1) == 1#1))))
  else
    (do
      let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_HCR_EL2_Type_VSE w__2) == 1#1))))


def ClearPendingVirtualSError (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VA w__1 0#1)))
  else
    (do
      let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__2 8 8 0#1))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPDefaultNaN (N : Nat) : SailM (BitVec N) := do
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr N))


def GPCRegistersConsistent (_ : Unit) : SailM Bool := do
  let w__3 ← (( do
    if ((← do
         let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
         (pure ((((_get_GPCCR_EL3_Type_PPS w__0) == 0b111#3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (DecodePPS ()) ) : SailM Int )
        let w__2 ← (( do (AArch64_PAMax ()) ) : SailM Int )
        (pure (((w__1 >b w__2) : Bool)))) ) : SailM Bool )
  if (w__3 : Bool)
  then (pure (false))
  else
    (do
      let w__4 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
      if (((_get_GPCCR_EL3_Type_PGS w__4) == 0b11#2) : Bool)
      then (pure (false))
      else
        (do
          let w__5 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
          if (((_get_GPCCR_EL3_Type_SH w__5) == 0b01#2) : Bool)
          then (pure (false))
          else
            (do
              let w__9 ← (( do
                if ((← do
                     let w__6 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                     let w__7 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                     (pure (((((_get_GPCCR_EL3_Type_ORGN w__6) +++ (_get_GPCCR_EL3_Type_IRGN w__7)) == 0b0000#4) : Bool)))) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_GPCCR_EL3_Type_SH w__8) != 0b10#2) : Bool))))
                else (pure false) ) : SailM Bool )
              let w__10 : Bool :=
                if (w__9 : Bool)
                then false
                else true
              (pure (w__10)))))


def RegimeUsingAArch32 (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL10 =>
    (do
      (ELUsingAArch32 EL1))
  | .Regime_EL30 => (pure (true))
  | .Regime_EL20 => (pure (false))
  | .Regime_EL2 =>
    (do
      (ELUsingAArch32 EL2))
  | .Regime_EL3 => (pure (false))


def AArch64_S1TTWParamsEL3 (_ : Unit) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1273) ()) ) : SailM S1TTWParams )
  let w__0 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let w__1 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL3_Type_TG0 w__0)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__1 } : S1TTWParams)
  let w__2 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_TCR_EL3_Type_T0SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL3_Type_PS w__3) } : S1TTWParams)
  let w__4 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_TCR_EL3_Type_IRGN0 w__4) } : S1TTWParams)
  let w__5 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_TCR_EL3_Type_ORGN0 w__5) } : S1TTWParams)
  let w__6 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_TCR_EL3_Type_SH0 w__6) } : S1TTWParams)
  let w__7 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with tbi := (_get_TCR_EL3_Type_TBI w__7) } : S1TTWParams)
  let w__8 ← (( do readReg MAIR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__8) } : S1TTWParams)
  let w__9 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg MAIR2_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__10) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__11 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let w__13 ← (( do
    if (w__11 : Bool)
    then
      (do
        let w__12 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_AIE w__12))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__13 } : S1TTWParams)
  let w__14 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL3_Type_WXN w__14) } : S1TTWParams)
  let w__15 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL3_Type_EE w__15) } : S1TTWParams)
  let w__18 ← (( do
    if ((← do
         let w__16 ← (( do (HaveRME ()) ) : SailM Bool )
         (pure (((! w__16) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (HaveSecureEL2Ext ())) ) : SailM Bool )
  let w__20 ← (( do
    if (w__18 : Bool)
    then
      (do
        let w__19 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_SCR_EL3_Type_SIF w__19))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with sif := w__20 } : S1TTWParams)
  let w__21 ← (( do (HavePACExt ()) ) : SailM Bool )
  let w__23 ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_TBID w__22))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tbid := w__23 } : S1TTWParams)
  let w__24 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
  let w__26 ← (( do
    if (w__24 : Bool)
    then
      (do
        let w__25 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HPD w__25))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hpd := w__26 } : S1TTWParams)
  let w__27 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__29 ← (( do
    if (w__27 : Bool)
    then
      (do
        let w__28 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HA w__28))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__29 } : S1TTWParams)
  let w__30 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__32 ← (( do
    if (w__30 : Bool)
    then
      (do
        let w__31 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HD w__31))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__32 } : S1TTWParams)
  let w__34 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__34 : Bool)
    then
      (do
        let w__35 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_TCR_EL3_Type_DS w__35) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__36 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__38 ← (( do
    if (w__36 : Bool)
    then
      (do
        let w__37 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_D128 w__37))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__38 } : S1TTWParams)
  let w__40 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__39 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TTBR0_EL3_Type_SKL w__39))))
    else (pure (0b00#2)) ) : SailM (BitVec 2) )
  let walkparams := ({ walkparams with skl := w__40 } : S1TTWParams)
  let w__42 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__41 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_DisCH0 w__41))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with disch := w__42 } : S1TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S1TTWParams := { walkparams with pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__43 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
        let w__45 ← (( do
          if (w__43 : Bool)
          then
            (do
              let w__44 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL3_Type_PIE w__44))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__45 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__46 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__46 : Bool)
    then
      (do
        let w__47 ← (( do readReg PIR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__47) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__48 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
  let w__50 ← (( do
    if (w__48 : Bool)
    then
      (do
        let w__49 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_MTX w__49))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with mtx := w__50 } : S1TTWParams)
  let w__52 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 == 0#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__52 : Bool)
    then
      (do
        let w__53 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pnch := (_get_TCR_EL3_Type_PnCH w__53) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__55 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  let walkparams ← (( do
    if (w__55 : Bool)
    then
      (do
        let w__56 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with haft := (_get_TCR_EL3_Type_HAFT w__56) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__57 ← (( do (HaveFeatMEC ()) ) : SailM Bool )
  let w__59 ← (( do
    if (w__57 : Bool)
    then
      (do
        let w__58 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL3_Type_EMEC w__58))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__59 } : S1TTWParams)
  (pure (walkparams))


end ArmFull.Functions
