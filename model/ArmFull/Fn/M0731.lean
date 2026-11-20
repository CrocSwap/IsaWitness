module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0071
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0136
public import ArmFull.Fn.M0137
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0258 set_option backward.proofsInPublic true @[expose] public section

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
def PMXEVCNTR_SysRegRead32_3357c1d37107c40d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T9 : (BitVec 1) := (_get_HSTR_EL2_Type_T9 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T9 : (BitVec 1) := (_get_HSTR_Type_T9 w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 w__7)
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__9)
  let w__10 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  if (((BitVec.toNat (_get_PMSELR_Type_SEL w__10)) ≥b 31) : Bool)
  then
    (do
      let w__11 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
      if (w__11 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__33 ← (( do
                if ((← do
                     let w__22 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                     (pure (((! w__22) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                         then
                           (do
                             let w__24 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__25 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             (pure (((((_get_PMUSERENR_EL0_Type_UEN w__24) +++ ((_get_PMUSERENR_EL0_Type_ER
                                       w__25) +++ (_get_PMUSERENR_EL0_Type_EN w__26))) == 0b000#3) : Bool))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((← do
                             let w__28 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool
                               )
                             (pure (((! w__28) : Bool)))) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                            (pure (((((_get_PMUSERENR_EL0_Type_ER w__29) +++ (_get_PMUSERENR_EL0_Type_EN
                                    w__30)) == 0b00#2) : Bool))))
                        else (pure false)))
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
                  let w__41 ← (( do
                    if ((← do
                         (ELUsingAArch32 EL1)) : Bool)
                    then
                      (do
                        let w__39 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                        let w__40 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_PMUSERENR_Type_ER w__39) +++ (_get_PMUSERENR_Type_EN w__40)) == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      let w__45 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__43 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__43) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__49 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__56 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__51 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__51) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__53) +++ (_get_HCR_EL2_Type_TGE
                                          w__54)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__56 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__60 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__72 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                if ((← do
                                                     if ((← do
                                                          (EL2Enabled ())) : Bool)
                                                     then
                                                       (do
                                                         let w__62 ← (( do (ELUsingAArch32 EL1) )
                                                           : SailM Bool )
                                                         (pure (((! w__62) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    let w__64 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    let w__65 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    (pure (((((_get_HCR_EL2_Type_E2H w__64) +++ (_get_HCR_EL2_Type_TGE
                                                            w__65)) != 0b11#2) : Bool))))
                                                else (pure false)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_FGT))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (pure ((← do
                                                let w__69 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                (pure (((! w__69) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                      else (pure false)) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
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
                                              let w__74 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__74) : Bool))))
                                          else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__76 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__80 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) )
                                        : SailM Bool )
                                      if (w__80 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__84 ← (( do
                                            if ((← do
                                                 (EL2Enabled ())) : Bool)
                                            then
                                              (do
                                                let w__82 ← (( do (PMSELR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                let w__83 ← (( do
                                                  (AArch32_GetNumEventCountersAccessible ()) ) :
                                                  SailM Int )
                                                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__82)) ≥b w__83) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__84 : Bool)
                                          then
                                            (do
                                              let w__85 ← (( do (IsFeatureImplemented FEAT_FGT) )
                                                : SailM Bool )
                                              if ((! w__85) : Bool)
                                              then
                                                (pure ((ConstrainUnpredictableProcedure
                                                    Unpredictable_PMUEVENTCOUNTER)))
                                              else
                                                (do
                                                  let w__86 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  if (w__86 : Bool)
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
                                              let w__90 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          let w__88 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__88) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__90 : Bool)
                                              then
                                                (do
                                                  let w__93 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__92 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__93 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__94 ← (( do (__get_selected_PMEVCNTR ()) )
                                                    : SailM (BitVec 32) )
                                                  (R_set t w__94))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__104 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__98 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__98) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__102 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__102) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__104 : Bool)
              then sailThrow ((Error_Undefined ()))
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
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__112 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__116 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__114 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__114) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__116 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__120 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__120 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__124 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
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
                                      let w__130 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__128 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__128) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__130 : Bool)
                                      then
                                        (do
                                          let w__133 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__132 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__132) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__133 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__134 ← (( do (__get_selected_PMEVCNTR ()) ) :
                                            SailM (BitVec 32) )
                                          (R_set t w__134)))))))))
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
                                         if ((← do
                                              (Halted ())) : Bool)
                                         then
                                           (do
                                             (HaveEL EL3))
                                         else (pure false)) : Bool)
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
                      let w__148 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__146 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__146) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__148 : Bool)
                      then
                        (do
                          let w__151 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__150 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__150) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__151 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__152 ← (( do (__get_selected_PMEVCNTR ()) ) : SailM (BitVec 32) )
                          (R_set t w__152))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__153 ← (( do (__get_selected_PMEVCNTR ()) ) : SailM (BitVec 32) )
                      (R_set t w__153))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def PMXEVTYPER_SysRegRead32_7d423ea169145383 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__9 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 w__9)
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
          let w__25 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__19 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__19) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__23 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__23) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__25 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__34 ← (( do
                if ((← do
                     let w__26 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                     (pure (((! w__26) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                         then
                           (do
                             let w__28 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__29 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             (pure (((((_get_PMUSERENR_EL0_Type_UEN w__28) +++ (_get_PMUSERENR_EL0_Type_EN
                                     w__29)) == 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              let w__31 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool
                                )
                              (pure (((! w__31) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__36 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__36) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__40 : Bool)
                  then
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__42) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__48 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__55 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__50 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__50) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__52 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__52) +++ (_get_HCR_EL2_Type_TGE
                                          w__53)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__55 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__59 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__59 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__71 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                if ((← do
                                                     if ((← do
                                                          (EL2Enabled ())) : Bool)
                                                     then
                                                       (do
                                                         let w__61 ← (( do (ELUsingAArch32 EL1) )
                                                           : SailM Bool )
                                                         (pure (((! w__61) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    let w__63 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    let w__64 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    (pure (((((_get_HCR_EL2_Type_E2H w__63) +++ (_get_HCR_EL2_Type_TGE
                                                            w__64)) != 0b11#2) : Bool))))
                                                else (pure false)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_FGT))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (pure ((← do
                                                let w__68 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                (pure (((! w__68) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                      else (pure false)) && ((__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__71 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__75 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__73 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__73) : Bool))))
                                          else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__75 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__79 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) )
                                        : SailM Bool )
                                      if (w__79 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__85 ← (( do
                                            if ((← do
                                                 if ((← do
                                                      (EL2Enabled ())) : Bool)
                                                 then
                                                   (do
                                                     let w__81 ← (( do (PMSELR_read ()) ) : SailM
                                                       (BitVec 32) )
                                                     (pure ((((BitVec.toNat
                                                           (_get_PMSELR_Type_SEL w__81)) != 31) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                let w__83 ← (( do (PMSELR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                let w__84 ← (( do
                                                  (AArch32_GetNumEventCountersAccessible ()) ) :
                                                  SailM Int )
                                                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__83)) ≥b w__84) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__85 : Bool)
                                          then
                                            (do
                                              let w__86 ← (( do (IsFeatureImplemented FEAT_FGT) )
                                                : SailM Bool )
                                              if ((! w__86) : Bool)
                                              then
                                                (pure ((ConstrainUnpredictableProcedure
                                                    Unpredictable_PMUEVENTCOUNTER)))
                                              else
                                                (do
                                                  let w__87 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  if (w__87 : Bool)
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
                                              let w__91 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          let w__89 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__89) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__91 : Bool)
                                              then
                                                (do
                                                  let w__94 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__93 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__93) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__94 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__95 ← (( do (PMSELR_read ()) ) : SailM
                                                    (BitVec 32) )
                                                  if (((BitVec.toNat (_get_PMSELR_Type_SEL w__95)) == 31) : Bool)
                                                  then
                                                    (do
                                                      let w__96 ← (( do (PMCCFILTR_read ()) ) :
                                                        SailM (BitVec 32) )
                                                      (R_set t (__get_PMCCFILTR w__96)))
                                                  else
                                                    (do
                                                      let w__97 ← (( do
                                                        (__get_selected_PMEVTYPER ()) ) : SailM
                                                        (BitVec 32) )
                                                      (R_set t (__get_PMEVTYPER w__97))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__107 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__101 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__101) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__105 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__105) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__107 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__111 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__109 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__109) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__111 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__115 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__115 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__119 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__117 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__117) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__119 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__123 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__123 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__129 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__125 ← (( do (PMSELR_read ()) ) : SailM
                                               (BitVec 32) )
                                             (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__125)) != 31) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__127 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32)
                                          )
                                        let w__128 ← (( do
                                          (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                                        (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__127)) ≥b w__128) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__129 : Bool)
                                  then
                                    (do
                                      let w__130 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM
                                        Bool )
                                      if ((! w__130) : Bool)
                                      then
                                        (pure ((ConstrainUnpredictableProcedure
                                            Unpredictable_PMUEVENTCOUNTER)))
                                      else
                                        (do
                                          let w__131 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          if (w__131 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))))
                                  else
                                    (do
                                      let w__135 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__133 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__133) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__135 : Bool)
                                      then
                                        (do
                                          let w__138 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__137 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__137) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__138 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__139 ← (( do (PMSELR_read ()) ) : SailM
                                            (BitVec 32) )
                                          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__139)) == 31) : Bool)
                                          then
                                            (do
                                              let w__140 ← (( do (PMCCFILTR_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_PMCCFILTR w__140)))
                                          else
                                            (do
                                              let w__141 ← (( do (__get_selected_PMEVTYPER ()) ) :
                                                SailM (BitVec 32) )
                                              (R_set t (__get_PMEVTYPER w__141)))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__151 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (Halted ())) : Bool)
                                         then
                                           (do
                                             (HaveEL EL3))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__145 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__145) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__149 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__149) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__151 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__155 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__153 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__153) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__155 : Bool)
                      then
                        (do
                          let w__158 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__157 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__157) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__158 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__159 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__159)) == 31) : Bool)
                          then
                            (do
                              let w__160 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
                              (R_set t (__get_PMCCFILTR w__160)))
                          else
                            (do
                              let w__161 ← (( do (__get_selected_PMEVTYPER ()) ) : SailM
                                (BitVec 32) )
                              (R_set t (__get_PMEVTYPER w__161))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__162 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                      if (((BitVec.toNat (_get_PMSELR_Type_SEL w__162)) == 31) : Bool)
                      then
                        (do
                          let w__163 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_PMCCFILTR w__163)))
                      else
                        (do
                          let w__164 ← (( do (__get_selected_PMEVTYPER ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_PMEVTYPER w__164))))
                  else (pure (()))))))


end ArmFull.Functions
