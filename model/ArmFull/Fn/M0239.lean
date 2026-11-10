import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0014
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0040
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0111
import ArmFull.Fn.M0113
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0158
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0194
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0204
import ArmFull.Fn.M0219
import ArmFull.Fn.M0226
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228

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

def SPEGetRandomBoolean (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (SPEGetRandomInterval ()) ) : SailM (BitVec 8) )
  (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 0)])) == 1#1)))


def BRBEExceptionReturn (target_address_in : (BitVec 64)) (source_el : (BitVec 2)) : SailM Unit := SailME.run do
  let target_address : (BitVec 64) := target_address_in
  let questionMark := source_el
  if ((questionMark == EL3) : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             let w__0 ← (( do (HaveBRBEv1p1 ()) ) : SailME Unit Bool )
             (pure (((! w__0) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__1 ← (( do readReg MDCR_EL3 ) : SailME Unit (BitVec 64) )
            let w__2 ← (( do readReg MDCR_EL3 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_MDCR_EL3_Type_E3BREC w__1) == (_get_MDCR_EL3_Type_E3BREW w__2)) : Bool))))
        ) : SailME Unit Bool )
      if (w__3 : Bool)
      then
        (do
          SailME.throw (() : Unit))
      else (pure (())))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          let w__4 ← (( do readReg BRBCR_EL2 ) : SailME Unit (BitVec 64) )
          if (((_get_BRBCR_EL2_Type_ERTN w__4) == 0#1) : Bool)
          then
            (do
              SailME.throw (() : Unit))
          else (pure (())))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__5 ← (( do readReg BRBCR_EL1 ) : SailME Unit (BitVec 64) )
              if (((_get_BRBCR_EL1_Type_ERTN w__5) == 0#1) : Bool)
              then
                (do
                  SailME.throw (() : Unit))
              else (pure (())))
          else (pure (()))))
  let source_valid ← (( do (BranchRecordAllowed source_el) ) : SailME Unit Bool )
  let w__6 ← (( do readReg PSTATE ) : SailME Unit ProcState )
  let target_valid ← (( do (BranchRecordAllowed w__6.EL) ) : SailME Unit Bool )
  let branch_valid : Bool := (source_valid || target_valid)
  if (branch_valid : Bool)
  then
    (do
      let branch_type : (BitVec 6) := 0b000111#6
      let ccu ← (( do (undefined_bitvector_at (← occLabel 2450) 1) ) : SailME Unit (BitVec 1) )
      let cc ← (( do (undefined_bitvector_at (← occLabel 2451) 14) ) : SailME Unit (BitVec 14) )
      let w__7 ← (( do (BranchEncCycleCount ()) ) : SailME Unit ((BitVec 1) × (BitVec 14)) )
      let (tup__0, tup__1) := (w__7 : ((BitVec 1) × (BitVec 14)))
      let ccu : (BitVec 1) := tup__0
      let cc : (BitVec 14) := tup__1
      let w__8 ← (( do (HaveTME ()) ) : SailME Unit Bool )
      let lastfailed ← (( do
        if (w__8 : Bool)
        then
          (do
            let w__9 ← (( do readReg BRBFCR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((_get_BRBFCR_EL1_Type_LASTFAILED w__9))))
        else (pure (0#1)) ) : SailME Unit (BitVec 1) )
      let w__13 ← (( do
        if ((← if (source_valid : Bool)
             then
               (do
                 (HaveTME ()))
             else (pure false)) : Bool)
        then
          (do
            let w__12 ← (( do readReg TSTATE ) : SailME Unit TMState )
            (pure (((w__12.depth >b 0) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      let transactional : (BitVec 1) :=
        if (w__13 : Bool)
        then 1#1
        else 0#1
      let el ← (( do
        if (target_valid : Bool)
        then
          (do
            let w__14 ← (( do readReg PSTATE ) : SailME Unit ProcState )
            (pure (w__14.EL)))
        else (pure (0b00#2)) ) : SailME Unit (BitVec 2) )
      let w__17 ← (( do
        (pure ((← if (source_valid : Bool)
              then
                (do
                  (BRBEMispredictAllowed ()))
              else (pure false)) && ((BranchMispredict ()) : Bool))) ) : SailME Unit Bool )
      let mispredict : (BitVec 1) :=
        if (w__17 : Bool)
        then 1#1
        else 0#1
      let sv : (BitVec 1) :=
        if (source_valid : Bool)
        then 1#1
        else 0#1
      let tv : (BitVec 1) :=
        if (target_valid : Bool)
        then 1#1
        else 0#1
      let source_address ← (( do
        if (source_valid : Bool)
        then
          (do
            (PC_read ()))
        else (pure ((Zeros (n := 64)))) ) : SailME Unit (BitVec 64) )
      let target_address : (BitVec 64) :=
        if ((! target_valid) : Bool)
        then (Zeros (n := 64))
        else target_address
      (UpdateBranchRecordBuffer ccu cc lastfailed transactional branch_type el mispredict
        (sv +++ tv) source_address target_address)
      let w__19 ← (( do readReg BRBFCR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__19 6 6 0#1)
      (PMUEvent PMU_EVENT_BRB_FILTRATE))
  else (pure (()))
  writeReg __last_branch_valid branch_valid


def BRB_INJ (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__2 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__4 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__5 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__6 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__7 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  let w__8 ← (( do readReg BRBSRCINJ_EL1 ) : SailM (BitVec 64) )
  let w__9 ← (( do readReg BRBTGTINJ_EL1 ) : SailM (BitVec 64) )
  (UpdateBranchRecordBuffer (_get_BRBINFINJ_EL1_Type_CCU w__0) (_get_BRBINFINJ_EL1_Type_CC w__1)
    (_get_BRBINFINJ_EL1_Type_LASTFAILED w__2) (_get_BRBINFINJ_EL1_Type_T w__3)
    (_get_BRBINFINJ_EL1_Type_TYPE w__4) (_get_BRBINFINJ_EL1_Type_EL w__5)
    (_get_BRBINFINJ_EL1_Type_MPRED w__6) (_get_BRBINFINJ_EL1_Type_VALID w__7)
    (_get_BRBSRCINJ_EL1_Type_ADDRESS w__8) (_get_BRBTGTINJ_EL1_Type_ADDRESS w__9))
  let w__10 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Mk_BRBINFINJ_EL1_Type w__10)
  let w__11 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg BRBSRCINJ_EL1 (Mk_BRBSRCINJ_EL1_Type w__11)
  let w__12 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg BRBTGTINJ_EL1 (Mk_BRBTGTINJ_EL1_Type w__12)
  let w__13 ← (( do (ConstrainUnpredictableBool Unpredictable_BRBFILTRATE) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_BRB_FILTRATE))
  else (pure (()))


def AArch32_GetS1TTWParams (regime : Regime) (va : (BitVec 32)) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 2507) ()) ) : SailM S1TTWParams )
  match regime with
  | .Regime_EL2 =>
    (do
      (AArch32_S1TTWParamsEL2 ()))
  | .Regime_EL10 =>
    (do
      (AArch32_S1TTWParamsEL10 va))
  | .Regime_EL30 =>
    (do
      (AArch32_S1TTWParamsEL30 va))
  | _ => (pure (walkparams))


def DCPSInstruction (target_el : (BitVec 2)) : SailM Unit := do
  let from_32 ← (( do (undefined_bool_at (← occLabel 2643) ()) ) : SailM Bool )
  let _ : Unit := (SynchronizeContext ())
  let handle_el ← (( do (undefined_bitvector_at (← occLabel 2644) 2) ) : SailM (BitVec 2) )
  let questionMark := target_el
  let handle_el ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        let w__4 ← (( do
          if ((← do
               let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__0.EL == EL2) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              if ((← do
                   let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__1.EL == EL3) : Bool)))) : Bool)
              then
                (do
                  let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                  (pure (((! w__2) : Bool))))
              else (pure false)) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
            let handle_el := (w__5.EL : (BitVec 2))
            (pure (handle_el)))
        else
          (do
            let w__8 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__7) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            if (w__8 : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (EL1))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            if ((! (HaveEL EL2)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else
              (do
                let w__11 ← (( do
                  if ((← do
                       let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__9.EL == EL3) : Bool)))) : Bool)
                  then
                    (do
                      let w__10 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                      (pure (((! w__10) : Bool))))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then (pure (EL3))
                else
                  (do
                    let w__14 ← (( do
                      if ((← do
                           let w__12 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
                           (pure (((! w__12) : Bool)))) : Bool)
                      then
                        (do
                          let w__13 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                          (pure (((BEq.beq w__13 SS_Secure) : Bool))))
                      else (pure false) ) : SailM Bool )
                    if (w__14 : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else (pure (EL2)))))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                let w__16 ← (( do
                  (pure ((← do
                        let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                        (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool)))) || ((! (HaveEL EL3)) : Bool)))
                  ) : SailM Bool )
                if (w__16 : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (EL3)))
            else
              (do
                (Unreachable ())
                (pure (handle_el))))) ) : SailM (BitVec 2) )
  let w__17 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let from_secure : Bool := (BEq.beq w__17 SS_Secure)
  let w__18 ← (( do (ELUsingAArch32 handle_el) ) : SailM Bool )
  if (w__18 : Bool)
  then
    (do
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__19.M == M32_Monitor) : Bool)
      then
        (do
          let w__20 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__20 0 0 0#1))
      else (pure (()))
      let w__21 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      ArmFull.assert w__21 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:39523.29-39523.30"
      let questionMark := handle_el
      if ((questionMark == EL1) : Bool)
      then
        (do
          (AArch32_WriteMode M32_Svc)
          let w__24 ← (( do
            if ((← do
                 (HavePANExt ())) : Bool)
            then
              (do
                let w__23 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                (pure ((((_get_SCTLR_Type_SPAN w__23) == 0#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__24 : Bool)
          then
            (do
              let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__25 with PAN := 1#1 })
          else (pure (())))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              (AArch32_WriteMode M32_Hyp))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  (AArch32_WriteMode M32_Monitor)
                  let w__26 ← (( do (HavePANExt ()) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      if ((! from_secure) : Bool)
                      then
                        (do
                          let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                          writeReg PSTATE { w__27 with PAN := 0#1 })
                      else
                        (do
                          let w__28 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                          if (((_get_SCTLR_Type_SPAN w__28) == 0#1) : Bool)
                          then
                            (do
                              let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__29 with PAN := 1#1 })
                          else (pure (()))))
                  else (pure (())))
              else (pure (()))))
      if ((handle_el == EL2) : Bool)
      then
        (do
          let w__30 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (ELR_hyp_write w__30)
          let w__31 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (HSR_write (Mk_HSR_Type w__31)))
      else
        (do
          let w__32 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (LR_write w__32))
      let w__33 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (SPSR_set (N := 32) w__33)
      let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__35 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
      writeReg PSTATE { w__34 with E := (_get_SCTLRType_EE w__35) }
      let w__36 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DLR_write w__36)
      let w__37 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__37)))
  else
    (do
      let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (from_32 : Bool)
      then
        (do
          (AArch64_MaybeZeroRegisterUppers ()))
      else (pure (()))
      let w__41 ← (( do
        if ((← if (from_32 : Bool)
             then
               (do
                 (HaveSME ()))
             else (pure false)) : Bool)
        then
          (do
            let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__40.SM == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__41 : Bool)
      then
        (do
          (ResetSVEState ()))
      else
        (do
          (MaybeZeroSVEUppers target_el))
      let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__42 with nRW := 0#1 }
      let w__43 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__43 with SP := 1#1 }
      let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__44 with EL := handle_el }
      let w__55 ← (( do
        if ((← do
             (HavePANExt ())) : Bool)
        then
          (do
            if ((← do
                 if (((handle_el == EL1) : Bool) : Bool)
                 then
                   (do
                     let w__46 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                     (pure ((((_get_SCTLR_EL1_Type_SPAN w__46) == 0#1) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     if ((← do
                          if (((handle_el == EL2) : Bool) : Bool)
                          then
                            (do
                              let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure ((((_get_HCR_EL2_Type_E2H w__48) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_TGE w__50) == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__52 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCTLR_EL2_Type_SPAN w__52) == 0#1) : Bool))))
                else (pure false)))
        else (pure false) ) : SailM Bool )
      if (w__55 : Bool)
      then
        (do
          let w__56 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__56 with PAN := 1#1 })
      else (pure (()))
      let w__57 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      (ELR_set__1 w__57)
      let w__58 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      (SPSR_set (N := 64) w__58)
      let w__59 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      (ESR_set__1 (Mk_ESRType w__59))
      let w__60 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__60
      let w__61 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__61)
      let w__62 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__62 : Bool)
      then
        (do
          let w__63 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__63 with UAO := 0#1 })
      else (pure (()))
      let w__64 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if (w__64 : Bool)
      then
        (do
          let w__65 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__65 with TCO := 1#1 })
      else (pure (()))
      let w__66 ← (( do (HaveGCS ()) ) : SailM Bool )
      if (w__66 : Bool)
      then
        (do
          let w__67 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__67 with EXLOCK := 0#1 })
      else (pure (())))
  (UpdateEDSCRFields ())
  let sync_errors ← (( do
    if ((← do
         (HaveIESB ())) : Bool)
    then
      (do
        let w__69 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_IESB w__69) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__72 ← (( do
    if ((← do
         (HaveDoubleFaultExt ())) : Bool)
    then
      (do
        let w__71 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__71) : Bool))))
    else (pure false) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__72 : Bool)
    then
      (do
        if ((sync_errors : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      let w__73 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
                      (pure (((w__73 == 1#1) : Bool)))) : Bool)
                 then
                   (do
                     let w__74 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_SCR_EL3_Type_NMEA w__74) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__76 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__76.EL == EL3) : Bool))))
            else (pure false)))
    else (pure (sync_errors)) ) : SailM Bool )
  let w__79 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
  let sync_errors : Bool :=
    if ((! w__79) : Bool)
    then false
    else sync_errors
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (pure (()))


def DebugRestorePSR (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let spsr ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
      (SetPSTATEFromPSR spsr)
      let split_vec ← (( do (__UNKNOWN_bits 13) ) : SailM (BitVec 13) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 12 12) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 11 11) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 10 10) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 9 9) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := (Sail.BitVec.extractLsb split_vec 8 8) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with GE := (Sail.BitVec.extractLsb split_vec 7 4) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with SS := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__9 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__10 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__11 with IT := 0b00000000#8 }
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with T := 1#1 }
      let w__13 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DLR_write w__13)
      let w__14 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__14)))
  else
    (do
      let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
      (SetPSTATEFromPSR spsr)
      let split_vec ← (( do (__UNKNOWN_bits 9) ) : SailM (BitVec 9) )
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__15 with N := (Sail.BitVec.extractLsb split_vec 8 8) }
      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__16 with Z := (Sail.BitVec.extractLsb split_vec 7 7) }
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with C := (Sail.BitVec.extractLsb split_vec 6 6) }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with V := (Sail.BitVec.extractLsb split_vec 5 5) }
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with SS := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__21 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__22 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__23 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      let w__24 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__24
      let w__25 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__25))
  (UpdateEDSCRFields ())


/-- Type quantifiers: n : Int -/
def AArch32_ReservedBreakpointType (n : Int) (bt_in : (BitVec 4)) : SailM (Constraint × (BitVec 4)) := SailME.run do
  let bt : (BitVec 4) := bt_in
  let reserved : Bool := false
  let b ← (( do (NumBreakpointsImplemented ()) ) : SailME (Constraint × (BitVec 4)) Int )
  let w__0 ← (( do (NumContextAwareBreakpointsImplemented b) ) : SailME (Constraint × (BitVec 4))
    Int )
  let context_aware : Bool := (n ≥b (b -i w__0))
  let w__2 ← (( do
    if ((let b__0 := bt
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) : Bool)
    then
      (do
        (HaltOnBreakpointOrWatchpoint ()))
    else (pure false) ) : SailME (Constraint × (BitVec 4)) Bool )
  let reserved : Bool :=
    if (w__2 : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if (((let b__1 := bt
         (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                    b__1 1 1)) == (0#1 : (BitVec 1)))) : Bool)
           then true
           else false : Bool))) && (! context_aware)) : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if (((let b__2 := bt
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (1#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) && (! (HaveEL EL2))) : Bool)
    then true
    else reserved
  let w__6 ← (( do
    if ((← do
         if ((let b__3 := bt
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
            then true
            else
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
              then true
              else false) : Bool)) : Bool)
         then
           (do
             let w__3 ← (( do (HaveVirtHostExt ()) ) : SailME (Constraint × (BitVec 4)) Bool )
             (pure (((! w__3) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do (HaveV82Debug ()) ) : SailME (Constraint × (BitVec 4)) Bool )
        (pure (((! w__5) : Bool))))
    else (pure false) ) : SailME (Constraint × (BitVec 4)) Bool )
  let reserved : Bool :=
    if (w__6 : Bool)
    then true
    else reserved
  let bt ← (( do
    if (reserved : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 2645) ()) ) : SailME
          (Constraint × (BitVec 4)) Constraint )
        let (choice, raw) ← (( do (C27bConstrainBP false context_aware) ) : SailME
          (Constraint × (BitVec 4)) (Constraint × (BitVec 5)) )
        let c : Constraint := choice
        let bt : (BitVec 4) := (Sail.BitVec.extractLsb raw 3 0)
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "/home/doug/boss-scratch/armcert-defects/c27b-accepted/armcert_c27b.sail:410.65-410.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            let w__7 ← (( do (__UNKNOWN_bits 4) ) : SailME (Constraint × (BitVec 4)) (BitVec 4) )
            SailME.throw ((c, w__7) : (Constraint × (BitVec 4))))
        else (pure (()))
        (pure (bt)))
    else (pure (bt)) ) : SailME (Constraint × (BitVec 4)) (BitVec 4) )
  (pure ((Constraint_NONE, bt)))


end ArmFull.Functions
