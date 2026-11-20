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
          let w__23 ← (( do
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
                                let w__17 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__17) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__21 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__21) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__32 ← (( do
                if ((← do
                     let w__24 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                     (pure (((! w__24) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                         then
                           (do
                             let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             let w__27 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                             (pure (((((_get_PMUSERENR_EL0_Type_UEN w__26) +++ (_get_PMUSERENR_EL0_Type_EN
                                     w__27)) == 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              let w__29 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool
                                )
                              (pure (((! w__29) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  let w__36 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__34 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__34) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__36 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__38 : Bool)
                  then
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__40) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__53 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__48 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__48) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__51 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__50) +++ (_get_HCR_EL2_Type_TGE
                                          w__51)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__53 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__57 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__57 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__69 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                if ((← do
                                                     if ((← do
                                                          (EL2Enabled ())) : Bool)
                                                     then
                                                       (do
                                                         let w__59 ← (( do (ELUsingAArch32 EL1) )
                                                           : SailM Bool )
                                                         (pure (((! w__59) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    let w__61 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    let w__62 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    (pure (((((_get_HCR_EL2_Type_E2H w__61) +++ (_get_HCR_EL2_Type_TGE
                                                            w__62)) != 0b11#2) : Bool))))
                                                else (pure false)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_FGT))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (pure ((← do
                                                let w__66 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                (pure (((! w__66) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                      else (pure false)) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__69 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__73 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__71 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__71) : Bool))))
                                          else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__73 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__77 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL2))
                                              else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) )
                                        : SailM Bool )
                                      if (w__77 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__81 ← (( do
                                            if ((← do
                                                 (EL2Enabled ())) : Bool)
                                            then
                                              (do
                                                let w__79 ← (( do (PMSELR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                let w__80 ← (( do
                                                  (AArch32_GetNumEventCountersAccessible ()) ) :
                                                  SailM Int )
                                                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__79)) ≥b w__80) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__81 : Bool)
                                          then
                                            (do
                                              let w__82 ← (( do (IsFeatureImplemented FEAT_FGT) )
                                                : SailM Bool )
                                              if ((! w__82) : Bool)
                                              then
                                                (pure ((ConstrainUnpredictableProcedure
                                                    Unpredictable_PMUEVENTCOUNTER)))
                                              else
                                                (do
                                                  let w__83 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  if (w__83 : Bool)
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
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
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
                                                  let w__91 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (__set_selected_PMEVCNTR w__91))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__101 ← (( do
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
                                    let w__95 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__95) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__99 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__99) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__101 : Bool)
              then sailThrow ((Error_Undefined ()))
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
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__109 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__113 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__111 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__111) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__113 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__117 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__117 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__121 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__119 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32)
                                          )
                                        let w__120 ← (( do
                                          (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                                        (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__119)) ≥b w__120) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__121 : Bool)
                                  then
                                    (do
                                      let w__122 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM
                                        Bool )
                                      if ((! w__122) : Bool)
                                      then
                                        (pure ((ConstrainUnpredictableProcedure
                                            Unpredictable_PMUEVENTCOUNTER)))
                                      else
                                        (do
                                          let w__123 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          if (w__123 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))))
                                  else
                                    (do
                                      let w__127 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__125 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__125) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__127 : Bool)
                                      then
                                        (do
                                          let w__130 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__129 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__129) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__130 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__131 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (__set_selected_PMEVCNTR w__131)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__141 ← (( do
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
                                        let w__135 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__135) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__139 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__139) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__141 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__145 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__143 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__143) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__145 : Bool)
                      then
                        (do
                          let w__148 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__147 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__147) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__148 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__149 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_selected_PMEVCNTR w__149))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__150 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_selected_PMEVCNTR w__150))
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
                                      else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool)))
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
                                                      let w__96 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (PMCCFILTR_write (Mk_PMCCFILTR_Type w__96)))
                                                  else
                                                    (do
                                                      let w__97 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (__set_selected_PMEVTYPER
                                                        (Mk_PMEVTYPER_Type w__97))))))))))))))
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
                                              let w__140 ← (( do (R_read t) ) : SailM (BitVec 32)
                                                )
                                              (PMCCFILTR_write (Mk_PMCCFILTR_Type w__140)))
                                          else
                                            (do
                                              let w__141 ← (( do (R_read t) ) : SailM (BitVec 32)
                                                )
                                              (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__141)))))))))))
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
                              let w__160 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (PMCCFILTR_write (Mk_PMCCFILTR_Type w__160)))
                          else
                            (do
                              let w__161 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__161))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__162 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                      if (((BitVec.toNat (_get_PMSELR_Type_SEL w__162)) == 31) : Bool)
                      then
                        (do
                          let w__163 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (PMCCFILTR_write (Mk_PMCCFILTR_Type w__163)))
                      else
                        (do
                          let w__164 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_selected_PMEVTYPER (Mk_PMEVTYPER_Type w__164))))
                  else (pure (()))))))


end ArmFull.Functions
