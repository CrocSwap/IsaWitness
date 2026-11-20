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
def PMEVCNTR_SysRegRead32_63ff5bc2709c8d46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__6)
  let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
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
                            let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__11) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__15 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__29 ← (( do
            if ((← do
                 let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__18) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__21 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__20) +++ ((_get_PMUSERENR_EL0_Type_ER
                                   w__21) +++ (_get_PMUSERENR_EL0_Type_EN w__22))) == 0b000#3) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         let w__24 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                         (pure (((! w__24) : Bool)))) : Bool)
                    then
                      (do
                        let w__25 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        (pure (((((_get_PMUSERENR_EL0_Type_ER w__25) +++ (_get_PMUSERENR_EL0_Type_EN
                                w__26)) == 0b00#2) : Bool))))
                    else (pure false)))
            else (pure false) ) : SailM Bool )
          if (w__29 : Bool)
          then
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__31) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__37 ← (( do
                if ((← do
                     (ELUsingAArch32 EL1)) : Bool)
                then
                  (do
                    let w__35 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    let w__36 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    (pure (((((_get_PMUSERENR_Type_ER w__35) +++ (_get_PMUSERENR_Type_EN w__36)) == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
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
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__57 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__47 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                               )
                                             (pure (((! w__47) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__49) +++ (_get_HCR_EL2_Type_TGE
                                                w__50)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__54 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__54) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__57 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__61 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__59 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__59) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__61 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__65 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__65 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__68 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__67 ← (( do (AArch32_GetNumEventCountersAccessible ()) )
                                      : SailM Int )
                                    (pure (((21 ≥b w__67) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__68 : Bool)
                              then
                                (do
                                  let w__69 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool
                                    )
                                  if ((! w__69) : Bool)
                                  then
                                    (pure ((ConstrainUnpredictableProcedure
                                        Unpredictable_PMUEVENTCOUNTER)))
                                  else
                                    (do
                                      let w__70 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                      if (w__70 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                              else
                                (do
                                  let w__74 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__72 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__72) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__74 : Bool)
                                  then
                                    (do
                                      let w__77 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__76 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__77 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__78 ← (( do (PMEVCNTR_read 21) ) : SailM (BitVec 32) )
                                      (R_set t w__78))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__88 ← (( do
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
                                let w__82 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__82) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__86 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__86) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__88 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__92 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__90 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__90) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__92 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__96 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__96 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__99 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__98 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((21 ≥b w__98) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__99 : Bool)
                      then
                        (do
                          let w__100 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__100) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              let w__101 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              if (w__101 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                      else
                        (do
                          let w__105 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__103 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__103) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__105 : Bool)
                          then
                            (do
                              let w__108 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__107 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__107) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__108 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__109 ← (( do (PMEVCNTR_read 21) ) : SailM (BitVec 32) )
                              (R_set t w__109)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__119 ← (( do
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
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__117 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__117) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__119 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__123 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__121 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__121) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__123 : Bool)
                  then
                    (do
                      let w__126 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__125 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__125) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__126 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__127 ← (( do (PMEVCNTR_read 21) ) : SailM (BitVec 32) )
                      (R_set t w__127))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__128 ← (( do (PMEVCNTR_read 21) ) : SailM (BitVec 32) )
                  (R_set t w__128))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegRead32_6a5d074d2473e341 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__6)
  let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
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
                            let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__11) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__15 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__29 ← (( do
            if ((← do
                 let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__18) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__21 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__20) +++ ((_get_PMUSERENR_EL0_Type_ER
                                   w__21) +++ (_get_PMUSERENR_EL0_Type_EN w__22))) == 0b000#3) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         let w__24 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                         (pure (((! w__24) : Bool)))) : Bool)
                    then
                      (do
                        let w__25 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        (pure (((((_get_PMUSERENR_EL0_Type_ER w__25) +++ (_get_PMUSERENR_EL0_Type_EN
                                w__26)) == 0b00#2) : Bool))))
                    else (pure false)))
            else (pure false) ) : SailM Bool )
          if (w__29 : Bool)
          then
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__31) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__37 ← (( do
                if ((← do
                     (ELUsingAArch32 EL1)) : Bool)
                then
                  (do
                    let w__35 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    let w__36 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    (pure (((((_get_PMUSERENR_Type_ER w__35) +++ (_get_PMUSERENR_Type_EN w__36)) == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
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
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__57 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__47 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                               )
                                             (pure (((! w__47) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__49) +++ (_get_HCR_EL2_Type_TGE
                                                w__50)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__54 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__54) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__57 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__61 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__59 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__59) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__61 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__65 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__65 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__68 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__67 ← (( do (AArch32_GetNumEventCountersAccessible ()) )
                                      : SailM Int )
                                    (pure (((30 ≥b w__67) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__68 : Bool)
                              then
                                (do
                                  let w__69 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool
                                    )
                                  if ((! w__69) : Bool)
                                  then
                                    (pure ((ConstrainUnpredictableProcedure
                                        Unpredictable_PMUEVENTCOUNTER)))
                                  else
                                    (do
                                      let w__70 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                      if (w__70 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                              else
                                (do
                                  let w__74 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__72 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__72) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__74 : Bool)
                                  then
                                    (do
                                      let w__77 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__76 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__77 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__78 ← (( do (PMEVCNTR_read 30) ) : SailM (BitVec 32) )
                                      (R_set t w__78))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__88 ← (( do
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
                                let w__82 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__82) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__86 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__86) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__88 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__92 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__90 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__90) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__92 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__96 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__96 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__99 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__98 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((30 ≥b w__98) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__99 : Bool)
                      then
                        (do
                          let w__100 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__100) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              let w__101 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              if (w__101 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
                      else
                        (do
                          let w__105 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__103 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__103) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__105 : Bool)
                          then
                            (do
                              let w__108 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__107 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__107) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__108 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__109 ← (( do (PMEVCNTR_read 30) ) : SailM (BitVec 32) )
                              (R_set t w__109)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__119 ← (( do
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
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__117 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__117) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__119 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__123 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__121 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__121) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__123 : Bool)
                  then
                    (do
                      let w__126 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__125 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__125) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__126 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__127 ← (( do (PMEVCNTR_read 30) ) : SailM (BitVec 32) )
                      (R_set t w__127))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__128 ← (( do (PMEVCNTR_read 30) ) : SailM (BitVec 32) )
                  (R_set t w__128))
              else (pure (())))))


end ArmFull.Functions
