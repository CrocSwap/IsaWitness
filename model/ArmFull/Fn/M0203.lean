import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0087
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0198

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

def ESR_set__1 (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  (ESR_set w__0 value_name)


def VBAR_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  (VBAR_read w__0)


def GenMPAMatEL (acctype : AccessType) (el : (BitVec 2)) : SailM MPAMinfo := SailME.run do
  let mpamEL ← (( do (undefined_bitvector_at (← occLabel 768) 2) ) : SailME MPAMinfo (BitVec 2)
    )
  let validEL_name : Bool := false
  let security ← (( do (SecurityStateAtEL el) ) : SailME MPAMinfo SecurityState )
  let InD : Bool := false
  let InSM : Bool := false
  let pspace : PARTIDspaceType := (PARTIDspaceFromSS security)
  let w__1 ← (( do
    if (((BEq.beq pspace PIdSpace_NonSecure) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (MPAMisEnabled ()) ) : SailME MPAMinfo Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailME MPAMinfo Bool )
  if (w__1 : Bool)
  then
    (do
      (DefaultMPAMinfo pspace))
  else
    (do
      let w__3 ← (( do (UsingAArch32 ()) ) : SailME MPAMinfo Bool )
      let (mpamEL, validEL_name) ← (( do
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do readReg PSTATE ) : SailME MPAMinfo ProcState )
            let w__5 ← (( do (ELFromM32 w__4.M) ) : SailME MPAMinfo (Bool × (BitVec 2)) )
            let (tup__0, tup__1) := (w__5 : (Bool × (BitVec 2)))
            let validEL_name : Bool := tup__0
            let mpamEL : (BitVec 2) := tup__1
            (pure ((mpamEL, validEL_name))))
        else
          (let mpamEL : (BitVec 2) :=
            if ((BEq.beq acctype AccessType_NV2) : Bool)
            then EL2
            else el
          let validEL_name : Bool := true
          (pure ((mpamEL, validEL_name)))) ) : SailME MPAMinfo ((BitVec 2) × Bool) )
      let (InD, InSM) ← (( do
        match acctype with
        | .AccessType_IFETCH =>
          (let InD : Bool := true
          (pure ((InD, InSM))))
        | .AccessType_IC =>
          (let InD : Bool := true
          (pure ((InD, InSM))))
        | .AccessType_SME =>
          (do
            let w__8 ← (( do
              if ((← do
                   (__IMPDEF_boolean "Shared SMCU")) : Bool)
              then (pure true)
              else
                (do
                  (__IMPDEF_boolean "MPAMSM_EL1 label precedence")) ) : SailME MPAMinfo Bool )
            let InSM := (w__8 : Bool)
            (pure ((InD, InSM))))
        | .AccessType_ASIMD =>
          (do
            let w__15 ← (( do
              if ((← do
                   if ((← do
                        (HaveSME ())) : Bool)
                   then
                     (do
                       let w__10 ← (( do readReg PSTATE ) : SailME MPAMinfo ProcState )
                       (pure (((w__10.SM == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  if ((← do
                       (__IMPDEF_boolean "Shared SMCU")) : Bool)
                  then (pure true)
                  else
                    (do
                      (__IMPDEF_boolean "MPAMSM_EL1 label precedence")))
              else (pure false) ) : SailME MPAMinfo Bool )
            let InSM := (w__15 : Bool)
            (pure ((InD, InSM))))
        | .AccessType_SVE =>
          (do
            let w__22 ← (( do
              if ((← do
                   if ((← do
                        (HaveSME ())) : Bool)
                   then
                     (do
                       let w__17 ← (( do readReg PSTATE ) : SailME MPAMinfo ProcState )
                       (pure (((w__17.SM == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  if ((← do
                       (__IMPDEF_boolean "Shared SMCU")) : Bool)
                  then (pure true)
                  else
                    (do
                      (__IMPDEF_boolean "MPAMSM_EL1 label precedence")))
              else (pure false) ) : SailME MPAMinfo Bool )
            let InSM := (w__22 : Bool)
            (pure ((InD, InSM))))
        | _ =>
          (let InD : Bool := false
          (pure ((InD, InSM)))) ) : SailME MPAMinfo (Bool × Bool) )
      if ((! validEL_name) : Bool)
      then
        (do
          (DefaultMPAMinfo pspace))
      else
        (do
          let w__26 ← (( do
            if ((← do
                 (HaveRME ())) : Bool)
            then
              (do
                let w__25 ← (( do readReg MPAMIDR_EL1 ) : SailME MPAMinfo (BitVec 64) )
                (pure ((((_get_MPAMIDR_EL1_Type_HAS_ALTSP w__25) == 1#1) : Bool))))
            else (pure false) ) : SailME MPAMinfo Bool )
          let pspace ← (( do
            if (w__26 : Bool)
            then
              (do
                (AltPARTIDspace mpamEL security pspace))
            else (pure (pspace)) ) : SailME MPAMinfo PARTIDspaceType )
          let w__30 ← (( do
            if ((← do
                 (HaveMPAMv0p1Ext ())) : Bool)
            then
              (do
                let w__29 ← (( do readReg MPAMIDR_EL1 ) : SailME MPAMinfo (BitVec 64) )
                (pure ((((_get_MPAMIDR_EL1_Type_HAS_FORCE_NS w__29) == 1#1) : Bool))))
            else (pure false) ) : SailME MPAMinfo Bool )
          let pspace ← (( do
            if (w__30 : Bool)
            then
              (do
                let w__32 ← (( do
                  (pure ((← do
                        let w__31 ← (( do (MPAM3_EL3_read ()) ) : SailME MPAMinfo (BitVec 64) )
                        (pure ((((_get_MPAM3_EL3_Type_FORCE_NS w__31) == 1#1) : Bool)))) && ((BEq.beq
                        security SS_Secure) : Bool))) ) : SailME MPAMinfo Bool )
                let pspace : PARTIDspaceType :=
                  if (w__32 : Bool)
                  then PIdSpace_NonSecure
                  else pspace
                (pure (pspace)))
            else (pure (pspace)) ) : SailME MPAMinfo PARTIDspaceType )
          let w__37 ← (( do
            if ((← do
                 if ((← do
                      (HaveMPAMv0p1Ext ())) : Bool)
                 then (pure true)
                 else
                   (do
                     (HaveMPAMv1p1Ext ()))) : Bool)
            then
              (do
                let w__36 ← (( do readReg MPAMIDR_EL1 ) : SailME MPAMinfo (BitVec 64) )
                (pure ((((_get_MPAMIDR_EL1_Type_HAS_SDEFLT w__36) == 1#1) : Bool))))
            else (pure false) ) : SailME MPAMinfo Bool )
          if (w__37 : Bool)
          then
            (do
              let w__39 ← (( do
                (pure ((← do
                      let w__38 ← (( do (MPAM3_EL3_read ()) ) : SailME MPAMinfo (BitVec 64) )
                      (pure ((((_get_MPAM3_EL3_Type_SDEFLT w__38) == 1#1) : Bool)))) && ((BEq.beq
                      security SS_Secure) : Bool))) ) : SailME MPAMinfo Bool )
              if (w__39 : Bool)
              then
                (do
                  let w__40 ← (( do (DefaultMPAMinfo pspace) ) : SailME MPAMinfo MPAMinfo )
                  SailME.throw (w__40 : MPAMinfo))
              else (pure (())))
          else (pure (()))
          let w__41 ← (( do (MPAMisEnabled ()) ) : SailME MPAMinfo Bool )
          if ((! w__41) : Bool)
          then
            (do
              (DefaultMPAMinfo pspace))
          else
            (do
              (genMPAM mpamEL InD InSM pspace))))


def AlignmentEnforced (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  let A ← (( do (undefined_bitvector_at (← occLabel 771) 1) ) : SailM (BitVec 1) )
  let A ← (( do
    match regime with
    | .Regime_EL3 =>
      (do
        let w__1 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
        let A := ((_get_SCTLR_EL3_Type_A w__1) : (BitVec 1))
        (pure (A)))
    | .Regime_EL30 =>
      (do
        let w__2 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
        let A := ((_get_SCTLR_Type_A w__2) : (BitVec 1))
        (pure (A)))
    | .Regime_EL2 =>
      (do
        let w__3 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HSCTLR_Type_A w__4))))
        else
          (do
            let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL2_Type_A w__5)))))
    | .Regime_EL20 =>
      (do
        let w__7 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        let A := ((_get_SCTLR_EL2_Type_A w__7) : (BitVec 1))
        (pure (A)))
    | .Regime_EL10 =>
      (do
        let w__8 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let w__9 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_A w__9))))
        else
          (do
            let w__10 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL1_Type_A w__10))))) ) : SailM (BitVec 1) )
  (pure ((A == 1#1)))


def EAEisOne (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (pure (((_get_TTBCR_Type_EAE w__0) == 1#1)))


def TTBR0_EL1_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _TTBR0_EL1 ) : SailM TTBR0_EL1_Type )
  let w__0 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 128))
  (pure (r))


def TTBR1_EL1_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _TTBR1_EL1 ) : SailM TTBR1_EL1_Type )
  let w__0 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 128))
  (pure (r))


def AArch32_EnterHypModeInDebugState (except : ExceptionRecord) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__3 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
             (pure (((BEq.beq w__0 SS_NonSecure) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ELUsingAArch32 EL2))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "sail-arm/v8_base.sail:13905.87-13905.88"
  (AArch32_ReportHypEntry except)
  (AArch32_WriteMode M32_Hyp)
  let w__4 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (SPSR_set (N := 32) w__4)
  let w__5 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (ELR_hyp_write w__5)
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with T := 1#1 }
  let split_vec ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with SS := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__11 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DLR_write w__11)
  let w__12 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DSPSR_write (Mk_DSPSR_Type w__12))
  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__14 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  writeReg PSTATE { w__13 with E := (_get_HSCTLR_Type_EE w__14) }
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__15 with IL := 0#1 }
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__16 with IT := 0b00000000#8 }
  let w__17 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__19 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
      writeReg PSTATE { w__18 with SSBS := w__19 })
  else (pure (()))
  let w__20 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ERR w__20 1#1))
  (UpdateEDSCRFields ())
  (EndOfInstruction ())


/-- Type quantifiers: n : Int -/
def R_set (n : Int) (value_name : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (Rmode_set n w__0.M value_name)


def ExcVectorBase (_ : Unit) : SailM (BitVec 32) := do
  let w__0 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  if (((_get_SCTLR_Type_V w__0) == 1#1) : Bool)
  then (pure (((Ones (n := 16)) +++ (Zeros (n := 16)))))
  else
    (do
      let w__1 ← (( do (VBAR_read__2 ()) ) : SailM (BitVec 32) )
      (pure (((Sail.BitVec.extractLsb w__1 31 5) +++ (Zeros (n := 5))))))


/-- Type quantifiers: k_route_to_monitor : Bool -/
def AArch32_ReportDataAbort (route_to_monitor : Bool) (fault : FaultRecord) (vaddress : (BitVec 32)) : SailM Unit := do
  let long_format ← (( do (undefined_bool_at (← occLabel 853) ()) ) : SailM Bool )
  let w__1 ← (( do
    if ((route_to_monitor : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((bne w__0 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  let long_format ← (( do
    if (w__1 : Bool)
    then
      (do
        if ((← do
             let w__2 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
             (pure ((((_get_TTBCR_Type_EAE w__2) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (IsExternalSyncAbort__1 fault)) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__4.EL == EL2) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__5 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
                         (pure ((((_get_TTBCR_Type_EAE w__5) == 1#1) : Bool))))) : Bool)
                then (pure true)
                else
                  (do
                    if ((fault.secondstage : Bool) : Bool)
                    then
                      (do
                        (__IMPDEF_boolean "Report abort using Long-descriptor format"))
                    else (pure false)))
            else (pure false)))
    else
      (do
        let w__12 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let long_format := (((_get_TTBCR_Type_EAE w__12) == 1#1) : Bool)
        (pure (long_format))) ) : SailM Bool )
  let syndrome ← (( do (AArch32_CommonFaultStatus fault long_format) ) : SailM (BitVec 32) )
  let syndrome : (BitVec 32) :=
    if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
             AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
    then
      (let syndrome : (BitVec 32) := (BitVec.update syndrome 13 (Bit 1#1))
      (BitVec.update syndrome 11 (Bit 1#1)))
    else
      (BitVec.update syndrome 11
        (Bit
          (if (fault.write : Bool)
          then 1#1
          else 0#1)))
  let syndrome : (BitVec 32) :=
    if ((! long_format) : Bool)
    then (Sail.BitVec.updateSubrange syndrome 7 4 fault.domain)
    else syndrome
  let syndrome ← (( do
    if ((BEq.beq fault.access.acctype AccessType_IC) : Bool)
    then
      (do
        let i_syndrome ← (( do (undefined_bitvector_at (← occLabel 854) 32) ) : SailM
          (BitVec 32) )
        let w__14 ← (( do
          if (((! long_format) : Bool) : Bool)
          then
            (do
              (__IMPDEF_boolean "Report I-cache maintenance fault in IFSR"))
          else (pure false) ) : SailM Bool )
        let (i_syndrome, syndrome) ← (( do
          if (w__14 : Bool)
          then
            (do
              let i_syndrome : (BitVec 32) := syndrome
              let split_vec ← (( do (EncodeSDFSC Fault_ICacheMaint 1) ) : SailM (BitVec 5) )
              let syndrome : (BitVec 32) :=
                (Sail.BitVec.updateSubrange syndrome 10 10 (Sail.BitVec.extractLsb split_vec 4 4))
              let syndrome : (BitVec 32) :=
                (Sail.BitVec.updateSubrange syndrome 3 0 (Sail.BitVec.extractLsb split_vec 3 0))
              (pure ((i_syndrome, syndrome))))
          else
            (do
              let w__15 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
              let i_syndrome := (w__15 : (BitVec 32))
              (pure ((i_syndrome, syndrome)))) ) : SailM ((BitVec 32) × (BitVec 32)) )
        if (route_to_monitor : Bool)
        then
          (do
            writeReg IFSR_S (Mk_IFSR_Type i_syndrome))
        else
          (do
            (IFSR_write (Mk_IFSR_Type i_syndrome)))
        (pure (syndrome)))
    else (pure (syndrome)) ) : SailM (BitVec 32) )
  if (route_to_monitor : Bool)
  then
    (do
      writeReg DFSR_S (Mk_DFSR_Type syndrome)
      (DFAR_S_write vaddress))
  else
    (do
      (DFSR_write (Mk_DFSR_Type syndrome))
      (DFAR_write vaddress))


/-- Type quantifiers: k_route_to_monitor : Bool -/
def AArch32_ReportPrefetchAbort (route_to_monitor : Bool) (fault : FaultRecord) (vaddress : (BitVec 32)) : SailM Unit := do
  let long_format : Bool := false
  let w__1 ← (( do
    if ((route_to_monitor : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((bne w__0 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  let long_format ← (( do
    if (w__1 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__2 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
                  (pure ((((_get_TTBCR_Type_EAE w__2) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__3.EL == EL2) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            let w__5 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_TTBCR_Type_EAE w__5) == 1#1) : Bool)))))
    else
      (do
        let w__7 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let long_format := (((_get_TTBCR_Type_EAE w__7) == 1#1) : Bool)
        (pure (long_format))) ) : SailM Bool )
  let fsr ← (( do (AArch32_CommonFaultStatus fault long_format) ) : SailM (BitVec 32) )
  if (route_to_monitor : Bool)
  then
    (do
      writeReg IFSR_S (Mk_IFSR_Type fsr)
      (IFAR_S_write vaddress))
  else
    (do
      (IFSR_write (Mk_IFSR_Type fsr))
      (IFAR_write vaddress))


def AArch64_AbortSyndrome (exceptype : Exception) (fault : FaultRecord) (vaddress : (BitVec 64)) (target_el : (BitVec 2)) : SailM ExceptionRecord := do
  let except ← (( do (ExceptionSyndrome exceptype) ) : SailM ExceptionRecord )
  let d_side : Bool :=
    ((BEq.beq exceptype Exception_DataAbort) || ((BEq.beq exceptype Exception_NV2DataAbort) || ((BEq.beq
            exceptype Exception_Watchpoint) || (BEq.beq exceptype Exception_NV2Watchpoint))))
  let w__7 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HavePFAR ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
             (pure (((! w__1) : Bool))))) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VM w__4) == 1#1) : Bool))))
              else (pure false)) && ((target_el == EL1) : Bool)))) ) : SailM Bool )
  let except ← (( do
    if (w__7 : Bool)
    then
      (let except : ExceptionRecord := { except with pavalid := false }
      (pure (except)))
    else
      (do
        let w__8 ← (( do (__IMPDEF_boolean "PFAR_ELx is valid") ) : SailM Bool )
        let except := ({ except with pavalid := w__8 } : ExceptionRecord)
        (pure (except))) ) : SailM ExceptionRecord )
  let w__9 ← (( do (AArch64_FaultSyndrome d_side fault except.pavalid) ) : SailM
    ((BitVec 25) × (BitVec 24)) )
  let (tup__0, tup__1) := (w__9 : ((BitVec 25) × (BitVec 24)))
  let except : ExceptionRecord := { except with syndrome := tup__0 }
  let except : ExceptionRecord := { except with syndrome2 := tup__1 }
  let except ← (( do
    if ((BEq.beq fault.statuscode Fault_TagCheck) : Bool)
    then
      (do
        let w__10 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        if (w__10 : Bool)
        then
          (let except : ExceptionRecord :=
            { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
          (pure (except)))
        else
          (do
            let w__11 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
            let except :=
              ({ except with vaddress := (w__11 +++ (Sail.BitVec.extractLsb vaddress 59 0)) } : ExceptionRecord)
            (pure (except))))
    else
      (let except : ExceptionRecord :=
        { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
      (pure (except))) ) : SailM ExceptionRecord )
  let w__12 ← (( do (IPAValid fault) ) : SailM Bool )
  let except : ExceptionRecord :=
    if (w__12 : Bool)
    then
      (let except : ExceptionRecord := { except with ipavalid := true }
      let except : ExceptionRecord :=
        { except with NS := if ((BEq.beq fault.ipaddress.paspace PAS_NonSecure) : Bool)
          then 1#1
          else 0#1 }
      { except with ipaddress := fault.ipaddress.address })
    else { except with ipavalid := false }
  (pure (except))


def IsMerging (fpcr : (BitVec 64)) : SailM Bool := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveSME ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.SM == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (IsFullA64Enabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let nep : (BitVec 1) :=
    if (w__4 : Bool)
    then 0#1
    else (_get_FPCRType_NEP fpcr)
  (pure ((← do
        if ((← do
             (HaveAltFP ())) : Bool)
        then
          (do
            let w__6 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__6) : Bool))))
        else (pure false)) && ((nep == 1#1) : Bool)))


def AArch32_CheckTimerConditions (_ : Unit) : SailM Unit := do
  let status ← (( do (undefined_bool_at (.site 1165) ()) ) : SailM Bool )
  let offset : (BitVec 64) := (Zeros (n := 64))
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert (! w__0) "sail-arm/v8_base.sail:18191.34-18191.35"
  let status ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        let w__1 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
        let status ← (( do
          if (((_get_CNTP_CTL_Type_ENABLE w__1) == 1#1) : Bool)
          then
            (do
              let w__2 ← (( do readReg CNTP_CVAL_S ) : SailM (BitVec 64) )
              let w__3 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
              let w__4 ← (( do
                (IsTimerConditionMet offset w__2 (_get_CNTP_CTL_Type_IMASK w__3) InterruptID_CNTPS)
                ) : SailM Bool )
              let status := (w__4 : Bool)
              let w__5 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
              writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange w__5 2 2
                (if (status : Bool)
                then 1#1
                else 0#1))
              (pure (status)))
          else (pure (status)) ) : SailM Bool )
        let w__6 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
        if (((_get_CNTP_CTL_Type_ENABLE w__6) == 1#1) : Bool)
        then
          (do
            let w__7 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
            let w__8 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
            let w__9 ← (( do
              (IsTimerConditionMet offset w__7 (_get_CNTP_CTL_Type_IMASK w__8) InterruptID_CNTP) ) :
              SailM Bool )
            let status := (w__9 : Bool)
            let w__10 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
            (CNTP_CTL_NS_write
              (_update_CNTP_CTL_Type_ISTATUS w__10
                (if (status : Bool)
                then 1#1
                else 0#1)))
            (pure (status)))
        else (pure (status)))
    else
      (do
        let w__11 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
        if (((_get_CNTP_CTL_Type_ENABLE w__11) == 1#1) : Bool)
        then
          (do
            let w__12 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
            let w__13 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
            let w__14 ← (( do
              (IsTimerConditionMet offset w__12 (_get_CNTP_CTL_Type_IMASK w__13) InterruptID_CNTP) )
              : SailM Bool )
            let status := (w__14 : Bool)
            let w__15 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
            (CNTP_CTL_write
              (_update_CNTP_CTL_Type_ISTATUS w__15
                (if (status : Bool)
                then 1#1
                else 0#1)))
            (pure (status)))
        else (pure (status))) ) : SailM Bool )
  let w__17 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        let w__16 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_CNTHP_CTL_Type_ENABLE w__16) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__17 : Bool)
    then
      (do
        let w__18 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
        let w__19 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        let w__20 ← (( do
          (IsTimerConditionMet offset w__18 (_get_CNTHP_CTL_Type_IMASK w__19) InterruptID_CNTHP) ) :
          SailM Bool )
        let status := (w__20 : Bool)
        let w__21 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        (CNTHP_CTL_write
          (_update_CNTHP_CTL_Type_ISTATUS w__21
            (if (status : Bool)
            then 1#1
            else 0#1)))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__22 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  if (((_get_CNTV_CTL_EL0_Type_ENABLE w__22) == 1#1) : Bool)
  then
    (do
      let w__23 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
      let w__24 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
      let w__25 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
      let status ← (( do
        (IsTimerConditionMet w__23 w__24 (_get_CNTV_CTL_EL0_Type_IMASK w__25) InterruptID_CNTV) ) :
        SailM Bool )
      let w__26 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
      writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__26 2 2
        (if (status : Bool)
        then 1#1
        else 0#1)))
  else (pure (()))


end ArmFull.Functions
