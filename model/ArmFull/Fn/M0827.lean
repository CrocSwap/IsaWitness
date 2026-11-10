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
import ArmFull.Fn.M0035
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059
import ArmFull.Fn.M0064
import ArmFull.Fn.M0071
import ArmFull.Fn.M0073
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0137
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0202
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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
def PMXEVCNTR_SysRegWrite32_4f0aa881614b1f11 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __PMUSERENR_EL0_EN : (BitVec 1) := (_get_PMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __PMUSERENR_EN : (BitVec 1) := (_get_PMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T9 : (BitVec 1) := (_get_HSTR_EL2_Type_T9 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T9 : (BitVec 1) := (_get_HSTR_Type_T9 w__7)
  let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__8)
  let w__9 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 w__9)
  let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__10)
  let w__11 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__11)
  let w__12 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  if (((BitVec.toNat (_get_PMSELR_Type_SEL w__12)) ≥b 31) : Bool)
  then
    (do
      let w__13 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__22 ← (( do
            (pure ((← do
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
                      let w__20 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__20) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__31 ← (( do
                if ((← do
                     let w__23 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                     (pure (((! w__23) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                         then
                           (do
                             let w__25 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             (pure (((((_get_PMUSERENR_EL0_Type_UEN w__25) +++ (_get_PMUSERENR_EL0_Type_EN
                                     w__26)) == 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              let w__28 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool
                                )
                              (pure (((! w__28) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__31 : Bool)
              then
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__33) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__37 : Bool)
                  then
                    (do
                      let w__41 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__39) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__41 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__45 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__45 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__47 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__47) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__49) +++ (_get_HCR_EL2_Type_TGE
                                          w__50)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__56 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (pure ((← do
                                            if ((← do
                                                 if ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          let w__58 ← (( do (ELUsingAArch32 EL1) )
                                                            : SailM Bool )
                                                          (pure (((! w__58) : Bool))))
                                                      else (pure false)) : Bool)
                                                 then
                                                   (do
                                                     let w__60 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     let w__61 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     (pure (((((_get_HCR_EL2_Type_E2H w__60) +++ (_get_HCR_EL2_Type_TGE
                                                             w__61)) != 0b11#2) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                (IsFeatureImplemented FEAT_FGT))
                                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__66 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__70 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__68) : Bool))))
                                          else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__70 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__74 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) )
                                        : SailM Bool )
                                      if (w__74 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__78 ← (( do
                                            if ((← do
                                                 (EL2Enabled ())) : Bool)
                                            then
                                              (do
                                                let w__76 ← (( do (PMSELR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                let w__77 ← (( do
                                                  (AArch32_GetNumEventCountersAccessible ()) ) :
                                                  SailM Int )
                                                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__76)) ≥b w__77) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__78 : Bool)
                                          then
                                            (do
                                              let w__79 ← (( do (IsFeatureImplemented FEAT_FGT) )
                                                : SailM Bool )
                                              if ((! w__79) : Bool)
                                              then
                                                (pure ((ConstrainUnpredictableProcedure
                                                    Unpredictable_PMUEVENTCOUNTER)))
                                              else
                                                (do
                                                  let w__80 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  if (w__80 : Bool)
                                                  then
                                                    (do
                                                      (AArch32_TakeHypTrapException
                                                        (BitVec.toNat 0x03#8)))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL2
                                                        (BitVec.toNat 0x03#8)))))
                                          else
                                            (do
                                              let w__83 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          let w__81 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__81) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__83 : Bool)
                                              then
                                                (do
                                                  let w__86 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__85 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__85) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__86 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__87 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (__set_selected_PMEVCNTR w__87))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__96 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__90 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__90) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__94 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__94) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__96 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__100 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__98 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__98) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__100 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__104 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__104 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__108 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__106 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__106) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__108 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__112 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__112 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__116 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__114 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32)
                                          )
                                        let w__115 ← (( do
                                          (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                                        (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__114)) ≥b w__115) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__116 : Bool)
                                  then
                                    (do
                                      let w__117 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM
                                        Bool )
                                      if ((! w__117) : Bool)
                                      then
                                        (pure ((ConstrainUnpredictableProcedure
                                            Unpredictable_PMUEVENTCOUNTER)))
                                      else
                                        (do
                                          let w__118 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          if (w__118 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))))
                                  else
                                    (do
                                      let w__121 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__119 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__119) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__121 : Bool)
                                      then
                                        (do
                                          let w__124 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__123 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__123) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__124 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__125 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (__set_selected_PMEVCNTR w__125)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__134 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__128 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__128) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__132 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__132) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__134 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__137 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__135 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__135) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__137 : Bool)
                      then
                        (do
                          let w__140 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__139 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__139) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__140 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__141 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_selected_PMEVCNTR w__141))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__142 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_selected_PMEVCNTR w__142))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def PMXEVTYPER_SysRegWrite32_853b58a36392d331 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __PMUSERENR_EL0_EN : (BitVec 1) := (_get_PMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __PMUSERENR_EN : (BitVec 1) := (_get_PMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T9 : (BitVec 1) := (_get_HSTR_EL2_Type_T9 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T9 : (BitVec 1) := (_get_HSTR_Type_T9 w__7)
  let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__8)
  let w__9 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 w__9)
  let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__10)
  let w__11 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__11)
  let w__14 ← (( do
    if ((← do
         let w__12 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
         (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__12)) != 31) : Bool)))) : Bool)
    then
      (do
        let w__13 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
        (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__13)) ≥b 31) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      let w__15 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
      if (w__15 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__24 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__18 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__18) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__22 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__22) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__24 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__33 ← (( do
                if ((← do
                     let w__25 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                     (pure (((! w__25) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                         then
                           (do
                             let w__27 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__28 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             (pure (((((_get_PMUSERENR_EL0_Type_UEN w__27) +++ (_get_PMUSERENR_EL0_Type_EN
                                     w__28)) == 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              let w__30 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool
                                )
                              (pure (((! w__30) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__35 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__35) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__39 : Bool)
                  then
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__41 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__41) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__47 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__47 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__49 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__49) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__51 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__52 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__51) +++ (_get_HCR_EL2_Type_TGE
                                          w__52)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__54 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__58 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__68 ← (( do
                                (pure ((← do
                                      (pure ((← do
                                            if ((← do
                                                 if ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          let w__60 ← (( do (ELUsingAArch32 EL1) )
                                                            : SailM Bool )
                                                          (pure (((! w__60) : Bool))))
                                                      else (pure false)) : Bool)
                                                 then
                                                   (do
                                                     let w__62 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     let w__63 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     (pure (((((_get_HCR_EL2_Type_E2H w__62) +++ (_get_HCR_EL2_Type_TGE
                                                             w__63)) != 0b11#2) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                (IsFeatureImplemented FEAT_FGT))
                                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__68 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__72 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__70 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__70) : Bool))))
                                          else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__72 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__76 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) )
                                        : SailM Bool )
                                      if (w__76 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__82 ← (( do
                                            if ((← do
                                                 if ((← do
                                                      (EL2Enabled ())) : Bool)
                                                 then
                                                   (do
                                                     let w__78 ← (( do (PMSELR_read ()) ) : SailM
                                                       (BitVec 32) )
                                                     (pure ((((BitVec.toNat
                                                           (_get_PMSELR_Type_SEL w__78)) != 31) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                let w__80 ← (( do (PMSELR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                let w__81 ← (( do
                                                  (AArch32_GetNumEventCountersAccessible ()) ) :
                                                  SailM Int )
                                                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__80)) ≥b w__81) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__82 : Bool)
                                          then
                                            (do
                                              let w__83 ← (( do (IsFeatureImplemented FEAT_FGT) )
                                                : SailM Bool )
                                              if ((! w__83) : Bool)
                                              then
                                                (pure ((ConstrainUnpredictableProcedure
                                                    Unpredictable_PMUEVENTCOUNTER)))
                                              else
                                                (do
                                                  let w__84 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  if (w__84 : Bool)
                                                  then
                                                    (do
                                                      (AArch32_TakeHypTrapException
                                                        (BitVec.toNat 0x03#8)))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL2
                                                        (BitVec.toNat 0x03#8)))))
                                          else
                                            (do
                                              let w__87 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          let w__85 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__85) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__87 : Bool)
                                              then
                                                (do
                                                  let w__90 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__89 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__89) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__90 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__91 ← (( do (PMSELR_read ()) ) : SailM
                                                    (BitVec 32) )
                                                  if (((BitVec.toNat (_get_PMSELR_Type_SEL w__91)) == 31) : Bool)
                                                  then
                                                    (do
                                                      let w__92 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (PMCCFILTR_write (Mk_PMCCFILTR_Type w__92)))
                                                  else
                                                    (do
                                                      let w__93 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (__set_selected_PMEVTYPER
                                                        (Mk_PMEVTYPER_Type w__93))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__102 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__96 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__96) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__100) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__102 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__106 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__104 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__104) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__106 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__110 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__110 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__114 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__112 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__112) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__114 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__118 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__118 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__124 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__120 ← (( do (PMSELR_read ()) ) : SailM
                                               (BitVec 32) )
                                             (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__120)) != 31) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__122 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32)
                                          )
                                        let w__123 ← (( do
                                          (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                                        (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__122)) ≥b w__123) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__124 : Bool)
                                  then
                                    (do
                                      let w__125 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM
                                        Bool )
                                      if ((! w__125) : Bool)
                                      then
                                        (pure ((ConstrainUnpredictableProcedure
                                            Unpredictable_PMUEVENTCOUNTER)))
                                      else
                                        (do
                                          let w__126 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          if (w__126 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))))
                                  else
                                    (do
                                      let w__129 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__127 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__127) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__129 : Bool)
                                      then
                                        (do
                                          let w__132 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__131 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__131) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__132 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__133 ← (( do (PMSELR_read ()) ) : SailM
                                            (BitVec 32) )
                                          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__133)) == 31) : Bool)
                                          then
                                            (do
                                              let w__134 ← (( do (R_read t) ) : SailM (BitVec 32)
                                                )
                                              (PMCCFILTR_write (Mk_PMCCFILTR_Type w__134)))
                                          else
                                            (do
                                              let w__135 ← (( do (R_read t) ) : SailM (BitVec 32)
                                                )
                                              (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__135)))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__144 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__138 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__138) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__142 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__142) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__144 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__147 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__145 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__145) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__147 : Bool)
                      then
                        (do
                          let w__150 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__149 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__149) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__150 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__151 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__151)) == 31) : Bool)
                          then
                            (do
                              let w__152 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (PMCCFILTR_write (Mk_PMCCFILTR_Type w__152)))
                          else
                            (do
                              let w__153 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__153))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__154 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                      if (((BitVec.toNat (_get_PMSELR_Type_SEL w__154)) == 31) : Bool)
                      then
                        (do
                          let w__155 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (PMCCFILTR_write (Mk_PMCCFILTR_Type w__155)))
                      else
                        (do
                          let w__156 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__156))))
                  else (pure (()))))))


end ArmFull.Functions
