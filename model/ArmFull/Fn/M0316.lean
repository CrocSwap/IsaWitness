import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0064
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0196
import ArmFull.Fn.M0246
import ArmFull.Fn.M0254

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

/-- Type quantifiers: t : Int -/
def DAIF_SysRegRead_102c97f1f2780854 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UMA : (BitVec 1) := (_get_SCTLR_EL1_Type_UMA w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__7 ← (( do
        (pure ((← do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool))))
              else (pure false)) || ((__SCTLR_EL1_UMA == 0#1) : Bool))) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          (X_set t 64
            (((Zeros (n := 54)) +++ (w__10.D +++ (w__11.A +++ (w__12.I +++ w__13.F)))) +++ (Zeros
                (n := 6))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
          (X_set t 64
            (((Zeros (n := 54)) +++ (w__14.D +++ (w__15.A +++ (w__16.I +++ w__17.F)))) +++ (Zeros
                (n := 6)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64
                (((Zeros (n := 54)) +++ (w__18.D +++ (w__19.A +++ (w__20.I +++ w__21.F)))) +++ (Zeros
                    (n := 6)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64
                    (((Zeros (n := 54)) +++ (w__22.D +++ (w__23.A +++ (w__24.I +++ w__25.F)))) +++ (Zeros
                        (n := 6)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGAUTHSTATUS_EL1_SysRegRead_d85001e86a493d96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGAUTHSTATUS_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_DBGAUTHSTATUS_EL1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__17 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__18 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__17) +++ (_get_MDCR_EL2_Type_TDA w__18)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__21 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__22 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_DBGAUTHSTATUS_EL1 w__22)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__31 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_DBGAUTHSTATUS_EL1 w__31)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__32 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DBGAUTHSTATUS_EL1 w__32)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_0eb0d62ea2fda071 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
             (pure (((15 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2) )
            let w__11 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((((15 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__28 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA
                                    w__27)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__28 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__31 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__31) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__35 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__35 : Bool)
                                  then
                                    (do
                                      let w__36 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__37 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      (X_set t 64
                                        (__get_DBGBCR_EL1
                                          (GetElem?.getElem! w__36
                                            (Sail.Int.toNatChecked ((15 +i ((BitVec.toNat w__37) *i 16))))))))
                                  else
                                    (do
                                      let w__38 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__38 15))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__46 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__50 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__47 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__47) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__50 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__51 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__51 : Bool)
                              then
                                (do
                                  let w__52 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__53 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  (X_set t 64
                                    (__get_DBGBCR_EL1
                                      (GetElem?.getElem! w__52
                                        (Sail.Int.toNatChecked ((15 +i ((BitVec.toNat w__53) *i 16))))))))
                              else
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__54 15))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__58 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__55 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__59 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__59 : Bool)
                          then
                            (do
                              let w__60 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__61 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              (X_set t 64
                                (__get_DBGBCR_EL1
                                  (GetElem?.getElem! w__60
                                    (Sail.Int.toNatChecked ((15 +i ((BitVec.toNat w__61) *i 16))))))))
                          else
                            (do
                              let w__62 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__62 15))))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_1e5042e13523fa5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
             (pure (((13 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2) )
            let w__11 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((((13 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__28 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA
                                    w__27)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__28 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__31 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__31) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__35 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__35 : Bool)
                                  then
                                    (do
                                      let w__36 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__37 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      (X_set t 64
                                        (__get_DBGBCR_EL1
                                          (GetElem?.getElem! w__36
                                            (Sail.Int.toNatChecked ((13 +i ((BitVec.toNat w__37) *i 16))))))))
                                  else
                                    (do
                                      let w__38 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__38 13))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__46 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__50 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__47 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__47) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__50 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__51 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__51 : Bool)
                              then
                                (do
                                  let w__52 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__53 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  (X_set t 64
                                    (__get_DBGBCR_EL1
                                      (GetElem?.getElem! w__52
                                        (Sail.Int.toNatChecked ((13 +i ((BitVec.toNat w__53) *i 16))))))))
                              else
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__54 13))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__58 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__55 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__59 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__59 : Bool)
                          then
                            (do
                              let w__60 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__61 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              (X_set t 64
                                (__get_DBGBCR_EL1
                                  (GetElem?.getElem! w__60
                                    (Sail.Int.toNatChecked ((13 +i ((BitVec.toNat w__61) *i 16))))))))
                          else
                            (do
                              let w__62 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! w__62 13))))))
                  else (pure (()))))))


end ArmFull.Functions
