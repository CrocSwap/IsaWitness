import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0069
import ArmFull.Fn.M0073
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0128
import ArmFull.Fn.M0132
import ArmFull.Fn.M0135
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
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
def SPMINTENSET_EL1_SysRegWrite_9368dd5ceffac1da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__2)
  let w__3 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMINTEN : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMINTEN w__3)
  let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (pure ((← do
                                  (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                       then
                         (do
                           let w__7 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__7) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (pure ((← do
                                     (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                          then
                            (do
                              let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__14) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__18 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__18 != 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
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
                                    (IsFeatureImplemented FEAT_FGT2))
                                else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__28 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGWTR2_EL2_nSPMINTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__28 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__30 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__30 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__33 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__32 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__32 != 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__33 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      let w__36 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__35 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__35) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__36 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__38 ← (( do
                                        if (((HaveEL EL3) : Bool) : Bool)
                                        then
                                          (do
                                            let w__37 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__37 != 0b11#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__38 : Bool)
                                      then
                                        (do
                                          let w__41 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__40 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__40) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__41 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__42 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          (pure ((SPMINTENSET_EL1_set
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__42))
                                              w__43))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__50 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                           then
                             (do
                               let w__46 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__50 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__58 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                              then
                                (do
                                  let w__53 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__53) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__57 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__57 != 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__58 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          let w__61 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__60 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__61 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__63 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                let w__62 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__62 != 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__65 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__65) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__67 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__68 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMINTENSET_EL1_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__67)) w__68))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__70 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMINTENSET_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__69))
                      w__70))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMOVSCLR_EL0_SysRegWrite_631efaee847d8a50 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__1)
  let w__2 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_EnSPM : (BitVec 1) := (_get_MDSCR_EL1_Type_EnSPM w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__4)
  let w__5 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMOVS : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMOVS w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        (pure ((← do
                              (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                   then
                     (do
                       let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                       (pure ((((_get_EDSCR_Type_SDD w__9) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           (pure ((← do
                                 (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                      then
                        (do
                          let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                let w__20 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM (BitVec 2) )
                (pure (((w__20 != 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__21 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
              then
                (do
                  let w__23 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__29 ← (( do
                    if ((← do
                         let w__27 ← (( do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE
                                       w__26)) == 0b11#2) : Bool))))
                           else (pure false) ) : SailM Bool )
                         (pure (((! w__27) : Bool)))) : Bool)
                    then
                      (do
                        let w__28 ← (( do (__get_selected_SPMACCESSR_EL1_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__28 != 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      let w__31 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__33 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__34 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__33) +++ (_get_HCR_EL2_Type_TGE
                                                     w__34)) != 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT2))
                                    else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           (pure (((((_get_HCR_EL2_Type_E2H w__41) +++ (_get_HCR_EL2_Type_TGE
                                                   w__42)) != 0b11#2) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsFeatureImplemented FEAT_FGT2))
                                  else (pure false)) && ((__HDFGWTR2_EL2_nSPMOVS == 0#1) : Bool))) )
                            : SailM Bool )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__51 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__50 ← (( do (__get_selected_SPMACCESSR_EL2_field ())
                                          ) : SailM (BitVec 2) )
                                        (pure (((w__50 != 0b11#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__51 : Bool)
                                  then
                                    (do
                                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                      then
                                        (do
                                          let w__54 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__53 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__53) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__54 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__56 ← (( do
                                            if (((HaveEL EL3) : Bool) : Bool)
                                            then
                                              (do
                                                let w__55 ← (( do
                                                  (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                                  (BitVec 2) )
                                                (pure (((w__55 != 0b11#2) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__56 : Bool)
                                          then
                                            (do
                                              let w__59 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__58 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__58) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__59 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_SystemAccessTrap EL3
                                                    (BitVec.toNat 0x18#8))))
                                          else
                                            (do
                                              let w__60 ← (( do readReg SPMSELR_EL0 ) : SailM
                                                (BitVec 64) )
                                              let w__61 ← (( do (X_read t 64) ) : SailM
                                                (BitVec 64) )
                                              (pure ((SPMOVSCLR_EL0_set
                                                  (BitVec.toNat
                                                    (_get_SPMSELR_EL0_Type_SYSPMUSEL w__60)) w__61))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__68 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (pure ((← do
                                  (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                       then
                         (do
                           let w__64 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__68 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__76 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (pure ((← do
                                     (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                          then
                            (do
                              let w__71 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__71) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__75 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__75 != 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__76 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__81 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT2))
                                else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__81 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__85 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGWTR2_EL2_nSPMOVS == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__85 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__87 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__87 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__90 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__89 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__89 != 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__90 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                                  then
                                    (do
                                      let w__93 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__92 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__93 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__95 ← (( do
                                        if (((HaveEL EL3) : Bool) : Bool)
                                        then
                                          (do
                                            let w__94 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__94 != 0b11#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__95 : Bool)
                                      then
                                        (do
                                          let w__98 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__97 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__97) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__98 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__99 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          let w__100 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          (pure ((SPMOVSCLR_EL0_set
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__99))
                                              w__100))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__107 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                           then
                             (do
                               let w__103 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__103) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__107 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__115 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                              then
                                (do
                                  let w__110 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__110) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__114 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__114 != 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__115 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                      then
                        (do
                          let w__118 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__117 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__117) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__118 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__120 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                let w__119 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__119 != 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__120 : Bool)
                          then
                            (do
                              let w__123 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__122 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__122) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__123 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__124 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__125 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMOVSCLR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__124)) w__125))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__126 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__127 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMOVSCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__126))
                      w__127))))
              else (pure (())))))


end ArmFull.Functions
