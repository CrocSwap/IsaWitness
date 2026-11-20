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
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0177
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
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
def PMCNTENSET_SysRegRead32_2d54f3b38c0729f6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HDFGRTR_EL2_PMCNTEN : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMCNTEN w__9)
  let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__10)
  let w__11 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__11)
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
          let w__30 ← (( do
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
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__24) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__25)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__27 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__27) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__30 : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__32) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__38) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__51 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__46 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__46) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__48) +++ (_get_HCR_EL2_Type_TGE
                                      w__49)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__51 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__55 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__55 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__67 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 if ((← do
                                                      (EL2Enabled ())) : Bool)
                                                 then
                                                   (do
                                                     let w__57 ← (( do (ELUsingAArch32 EL1) ) :
                                                       SailM Bool )
                                                     (pure (((! w__57) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                let w__59 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                let w__60 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                (pure (((((_get_HCR_EL2_Type_E2H w__59) +++ (_get_HCR_EL2_Type_TGE
                                                        w__60)) != 0b11#2) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_FGT))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (pure ((← do
                                            let w__64 ← (( do (HaveEL EL3) ) : SailM Bool )
                                            (pure (((! w__64) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                  else (pure false)) && ((__HDFGRTR_EL2_PMCNTEN == 1#1) : Bool))) )
                            : SailM Bool )
                          if (w__67 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__71 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__69 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__69) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
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
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__75 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__79 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__77 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__77) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__79 : Bool)
                                      then
                                        (do
                                          let w__82 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__81 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__82 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__83 ← (( do (PMCNTENSET_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__83)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__93 ← (( do
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
                                let w__87 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__87) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__91 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__91) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__93 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__97 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__95 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__95) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
              if (w__97 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__101 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__101 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__105 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__103 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__103) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__105 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__109 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__109 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__113 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__111 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__111) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__113 : Bool)
                              then
                                (do
                                  let w__116 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__115 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__115) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__116 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__117 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                                  (R_set t w__117))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__127 ← (( do
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
                                    let w__121 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__121) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__125 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__125) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__127 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__131 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__129 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__129) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__131 : Bool)
                  then
                    (do
                      let w__134 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__133 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__133) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__134 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__135 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                      (R_set t w__135))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__136 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__136))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMCR_SysRegRead32_fb694f2a3eabe8b5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPMCR : (BitVec 1) := (_get_MDCR_EL2_Type_TPMCR w__9)
  let w__10 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__10)
  let w__11 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPMCR : (BitVec 1) := (_get_HDCR_Type_TPMCR w__11)
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
          let w__30 ← (( do
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
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__24) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__25)) != 0b01#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__27 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__27) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__30 : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__32) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__38) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__51 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__46 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__46) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__48) +++ (_get_HCR_EL2_Type_TGE
                                      w__49)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__51 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__55 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__55 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__59 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__57 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__57) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__59 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__63 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__61 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__61) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TPMCR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__63 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__67 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__67 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__71 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPMCR == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__71 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__75 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__73 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__73) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__75 : Bool)
                                          then
                                            (do
                                              let w__78 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__77 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__77) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__78 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__79 ← (( do (PMCR_read ()) ) : SailM
                                                (BitVec 32) )
                                              let w__80 ← (( do (__get_PMCR w__79) ) : SailM
                                                (BitVec 32) )
                                              (R_set t w__80))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__90 ← (( do
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
                                let w__84 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__84) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__88 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__88) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__90 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__94 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__92 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__92) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
              if (w__94 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__98 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__98 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__102 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__100 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__100) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__102 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
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
                                  else (pure false)) && ((__MDCR_EL2_TPMCR == 1#1) : Bool))) ) :
                            SailM Bool )
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
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
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
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPMCR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__114 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__118 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__116 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__116) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__118 : Bool)
                                      then
                                        (do
                                          let w__121 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__120 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__121 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__122 ← (( do (PMCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          let w__123 ← (( do (__get_PMCR w__122) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__123))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__133 ← (( do
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
                                    let w__127 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__131 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__131) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__133 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__137 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__135 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__135) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                      let w__141 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                      let w__142 ← (( do (__get_PMCR w__141) ) : SailM (BitVec 32) )
                      (R_set t w__142))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__143 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                  let w__144 ← (( do (__get_PMCR w__143) ) : SailM (BitVec 32) )
                  (R_set t w__144))
              else (pure (())))))


end ArmFull.Functions
