import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0050
import ArmFull.Fn.M0064
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
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
def DBGBCR_EL1_SysRegWrite_ff386e82c1b05d03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 w__4)
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
             (pure (((4 ≥b w__7) : Bool))))
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
            (pure ((((4 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
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
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
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
                                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__36
                                        (Sail.Int.toNatChecked ((4 +i ((BitVec.toNat w__37) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__38)))
                                  else
                                    (do
                                      let w__39 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__39 4
                                        (Mk_DBGBCR_EL1_Type w__40)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__46 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__46 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__48 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__49 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__49) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__53 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__55 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__54
                                    (Sail.Int.toNatChecked ((4 +i ((BitVec.toNat w__55) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__56)))
                              else
                                (do
                                  let w__57 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__57 4
                                    (Mk_DBGBCR_EL1_Type w__58)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__59 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__59) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__62 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__63 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__64 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__65 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__64
                                (Sail.Int.toNatChecked ((4 +i ((BitVec.toNat w__65) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__66)))
                          else
                            (do
                              let w__67 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__68 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__67 4 (Mk_DBGBCR_EL1_Type w__68)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ffc42f78aa082453 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 w__4)
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
             (pure (((14 ≥b w__7) : Bool))))
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
            (pure ((((14 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
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
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
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
                                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__36
                                        (Sail.Int.toNatChecked ((14 +i ((BitVec.toNat w__37) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__38)))
                                  else
                                    (do
                                      let w__39 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__39 14
                                        (Mk_DBGBCR_EL1_Type w__40)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__46 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__46 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__48 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__49 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__49) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__53 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__55 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__54
                                    (Sail.Int.toNatChecked ((14 +i ((BitVec.toNat w__55) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__56)))
                              else
                                (do
                                  let w__57 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__57 14
                                    (Mk_DBGBCR_EL1_Type w__58)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__59 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__59) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__62 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__63 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__64 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__65 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__64
                                (Sail.Int.toNatChecked ((14 +i ((BitVec.toNat w__65) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__66)))
                          else
                            (do
                              let w__67 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__68 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__67 14 (Mk_DBGBCR_EL1_Type w__68)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_ffdc1fc8f6c7fc45 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 w__4)
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
             (pure (((12 ≥b w__7) : Bool))))
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
            (pure ((((12 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
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
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
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
                                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__36
                                        (Sail.Int.toNatChecked ((12 +i ((BitVec.toNat w__37) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__38)))
                                  else
                                    (do
                                      let w__39 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__39 12
                                        (Mk_DBGBCR_EL1_Type w__40)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__46 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__46 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__48 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__49 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__49) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__53 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__55 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__54
                                    (Sail.Int.toNatChecked ((12 +i ((BitVec.toNat w__55) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__56)))
                              else
                                (do
                                  let w__57 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__57 12
                                    (Mk_DBGBCR_EL1_Type w__58)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__59 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__59) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__62 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__63 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__64 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__65 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__64
                                (Sail.Int.toNatChecked ((12 +i ((BitVec.toNat w__65) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__66)))
                          else
                            (do
                              let w__67 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__68 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__67 12 (Mk_DBGBCR_EL1_Type w__68)))))
                  else (pure (()))))))


end ArmFull.Functions
