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
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0201
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
def PMEVCNTR_SysRegWrite32_1402236c25c3ee30 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 w__7)
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
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
                            let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__28 ← (( do
            if ((← do
                 let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__20) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__23 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__22) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__23)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__25 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__25) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__28 : Bool)
          then
            (do
              let w__32 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__30) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__34 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
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
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
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
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                               )
                                             (pure (((! w__44) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                w__47)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__51) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
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
                                  let w__56 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__56) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__65 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__64 ← (( do (AArch32_GetNumEventCountersAccessible ()) )
                                      : SailM Int )
                                    (pure (((3 ≥b w__64) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__65 : Bool)
                              then
                                (do
                                  let w__66 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool
                                    )
                                  if ((! w__66) : Bool)
                                  then
                                    (pure ((ConstrainUnpredictableProcedure
                                        Unpredictable_PMUEVENTCOUNTER)))
                                  else
                                    (do
                                      let w__67 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                      if (w__67 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                              else
                                (do
                                  let w__71 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__69 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__69) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__71 : Bool)
                                  then
                                    (do
                                      let w__74 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__73 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__74 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (PMEVCNTR_set 3 w__75))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__85 ← (( do
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
                                let w__79 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__79) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__83 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__83) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__85 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__89 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__87 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__87) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__89 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__93 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__93 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__96 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__95 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((3 ≥b w__95) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__96 : Bool)
                      then
                        (do
                          let w__97 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__97) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              let w__98 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              if (w__98 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__100) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              let w__105 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__104 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__105 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__106 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (PMEVCNTR_set 3 w__106)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__116 ← (( do
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
                                    let w__110 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__110) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__114 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__114) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__116 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__120 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__118 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__118) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__124 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMEVCNTR_set 3 w__124))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__125 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMEVCNTR_set 3 w__125))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_1b282b60cc4c6447 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 w__7)
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
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
                            let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__28 ← (( do
            if ((← do
                 let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__20) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__23 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__22) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__23)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__25 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__25) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__28 : Bool)
          then
            (do
              let w__32 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__30) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__34 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
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
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
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
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                               )
                                             (pure (((! w__44) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                w__47)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__51) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
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
                                  let w__56 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__56) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__65 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__64 ← (( do (AArch32_GetNumEventCountersAccessible ()) )
                                      : SailM Int )
                                    (pure (((20 ≥b w__64) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__65 : Bool)
                              then
                                (do
                                  let w__66 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool
                                    )
                                  if ((! w__66) : Bool)
                                  then
                                    (pure ((ConstrainUnpredictableProcedure
                                        Unpredictable_PMUEVENTCOUNTER)))
                                  else
                                    (do
                                      let w__67 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                      if (w__67 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                              else
                                (do
                                  let w__71 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__69 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__69) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__71 : Bool)
                                  then
                                    (do
                                      let w__74 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__73 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__74 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (PMEVCNTR_set 20 w__75))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__85 ← (( do
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
                                let w__79 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__79) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__83 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__83) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__85 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__89 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__87 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__87) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__89 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__93 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__93 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__96 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__95 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((20 ≥b w__95) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__96 : Bool)
                      then
                        (do
                          let w__97 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__97) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              let w__98 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              if (w__98 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__100) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              let w__105 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__104 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__105 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__106 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (PMEVCNTR_set 20 w__106)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__116 ← (( do
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
                                    let w__110 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__110) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__114 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__114) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__116 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__120 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__118 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__118) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__124 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMEVCNTR_set 20 w__124))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__125 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMEVCNTR_set 20 w__125))
              else (pure (())))))


end ArmFull.Functions
