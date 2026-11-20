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
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0128
public import ArmFull.Fn.M0132
public import ArmFull.Fn.M0135
public import ArmFull.Fn.M0142
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0252 set_option backward.proofsInPublic true @[expose] public section

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
def SPMCNTENCLR_EL0_SysRegRead_1114ed6fac10af30 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nSPMCNTEN : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nSPMCNTEN w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
        (pure ((← do
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
                       let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                       (pure ((((_get_EDSCR_Type_SDD w__10) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__23 ← (( do
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
                          let w__18 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__18) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                let w__22 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM (BitVec 2) )
                (pure (((w__22 == 0b00#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__31 ← (( do
                    if ((← do
                         let w__29 ← (( do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure (((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE
                                       w__28)) == 0b11#2) : Bool))))
                           else (pure false) ) : SailM Bool )
                         (pure (((! w__29) : Bool)))) : Bool)
                    then
                      (do
                        let w__30 ← (( do (__get_selected_SPMACCESSR_EL1_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__30 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            let w__35 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__36 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE
                                                    w__36)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT2))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (HaveEL EL3))
                              else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           (pure (((((_get_HCR_EL2_Type_E2H w__44) +++ (_get_HCR_EL2_Type_TGE
                                                   w__45)) != 0b11#2) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsFeatureImplemented FEAT_FGT2))
                                  else (pure false)) && ((__HDFGRTR2_EL2_nSPMCNTEN == 0#1) : Bool)))
                            ) : SailM Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__51 ← (( do
                                (pure ((← do
                                      (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__51 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__54 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__53 ← (( do (__get_selected_SPMACCESSR_EL2_field ())
                                          ) : SailM (BitVec 2) )
                                        (pure (((w__53 == 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      let w__56 ← (( do
                                        (pure ((← do
                                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool)))
                                        ) : SailM Bool )
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
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__62 ← (( do
                                            if ((← do
                                                 (HaveEL EL3)) : Bool)
                                            then
                                              (do
                                                let w__61 ← (( do
                                                  (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                                  (BitVec 2) )
                                                (pure (((w__61 == 0b00#2) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__62 : Bool)
                                          then
                                            (do
                                              let w__65 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__64 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__65 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_SystemAccessTrap EL3
                                                    (BitVec.toNat 0x18#8))))
                                          else
                                            (do
                                              let w__66 ← (( do readReg SPMSELR_EL0 ) : SailM
                                                (BitVec 64) )
                                              (X_set t 64
                                                (SPMCNTENCLR_EL0_read
                                                  (BitVec.toNat
                                                    (_get_SPMSELR_EL0_Type_SYSPMUSEL w__66)))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__74 ← (( do
            (pure ((← do
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
                           let w__70 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__70) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__74 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__83 ← (( do
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
                              let w__78 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__82 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__82 == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__83 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__89 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT2))
                               else (pure false)) : Bool)
                          then
                            (do
                              (HaveEL EL3))
                          else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__89 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__93 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGRTR2_EL2_nSPMCNTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__93 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__95 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__95 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__98 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__97 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__97 == 0b00#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__98 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__100 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__100 : Bool)
                                  then
                                    (do
                                      let w__103 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__102 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__102) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__103 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__106 ← (( do
                                        if ((← do
                                             (HaveEL EL3)) : Bool)
                                        then
                                          (do
                                            let w__105 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__105 == 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__106 : Bool)
                                      then
                                        (do
                                          let w__109 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__108 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__108) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__109 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__110 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64
                                            (SPMCNTENCLR_EL0_read
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__110)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__118 ← (( do
                (pure ((← do
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
                               let w__114 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__114) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__118 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__127 ← (( do
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
                                  let w__122 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__122) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__126 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__126 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__127 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__129 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                      if (w__129 : Bool)
                      then
                        (do
                          let w__132 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__131 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__131) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__132 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__135 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                let w__134 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__134 == 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__135 : Bool)
                          then
                            (do
                              let w__138 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__137 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__137) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__138 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__139 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (SPMCNTENCLR_EL0_read
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__139)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__140 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64
                    (SPMCNTENCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__140)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMCNTENSET_EL0_SysRegRead_d76b56a27ec0166e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nSPMCNTEN : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nSPMCNTEN w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
        (pure ((← do
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
                       let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                       (pure ((((_get_EDSCR_Type_SDD w__10) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__23 ← (( do
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
                          let w__18 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__18) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                let w__22 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM (BitVec 2) )
                (pure (((w__22 == 0b00#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__31 ← (( do
                    if ((← do
                         let w__29 ← (( do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure (((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE
                                       w__28)) == 0b11#2) : Bool))))
                           else (pure false) ) : SailM Bool )
                         (pure (((! w__29) : Bool)))) : Bool)
                    then
                      (do
                        let w__30 ← (( do (__get_selected_SPMACCESSR_EL1_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__30 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            let w__35 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__36 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE
                                                    w__36)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT2))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (HaveEL EL3))
                              else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64)
                                             )
                                           (pure (((((_get_HCR_EL2_Type_E2H w__44) +++ (_get_HCR_EL2_Type_TGE
                                                   w__45)) != 0b11#2) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsFeatureImplemented FEAT_FGT2))
                                  else (pure false)) && ((__HDFGRTR2_EL2_nSPMCNTEN == 0#1) : Bool)))
                            ) : SailM Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__51 ← (( do
                                (pure ((← do
                                      (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__51 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__54 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__53 ← (( do (__get_selected_SPMACCESSR_EL2_field ())
                                          ) : SailM (BitVec 2) )
                                        (pure (((w__53 == 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      let w__56 ← (( do
                                        (pure ((← do
                                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool)))
                                        ) : SailM Bool )
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
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__62 ← (( do
                                            if ((← do
                                                 (HaveEL EL3)) : Bool)
                                            then
                                              (do
                                                let w__61 ← (( do
                                                  (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                                  (BitVec 2) )
                                                (pure (((w__61 == 0b00#2) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__62 : Bool)
                                          then
                                            (do
                                              let w__65 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__64 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__65 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_SystemAccessTrap EL3
                                                    (BitVec.toNat 0x18#8))))
                                          else
                                            (do
                                              let w__66 ← (( do readReg SPMSELR_EL0 ) : SailM
                                                (BitVec 64) )
                                              (X_set t 64
                                                (SPMCNTENSET_EL0_read
                                                  (BitVec.toNat
                                                    (_get_SPMSELR_EL0_Type_SYSPMUSEL w__66)))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__74 ← (( do
            (pure ((← do
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
                           let w__70 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__70) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__74 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__83 ← (( do
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
                              let w__78 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__82 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__82 == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__83 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__89 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT2))
                               else (pure false)) : Bool)
                          then
                            (do
                              (HaveEL EL3))
                          else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__89 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__93 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGRTR2_EL2_nSPMCNTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__93 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__95 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__95 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__98 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__97 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__97 == 0b00#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__98 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__100 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__100 : Bool)
                                  then
                                    (do
                                      let w__103 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__102 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__102) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__103 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__106 ← (( do
                                        if ((← do
                                             (HaveEL EL3)) : Bool)
                                        then
                                          (do
                                            let w__105 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__105 == 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__106 : Bool)
                                      then
                                        (do
                                          let w__109 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__108 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__108) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__109 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__110 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64
                                            (SPMCNTENSET_EL0_read
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__110)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__118 ← (( do
                (pure ((← do
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
                               let w__114 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__114) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__118 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__127 ← (( do
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
                                  let w__122 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__122) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__126 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__126 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__127 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__129 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                      if (w__129 : Bool)
                      then
                        (do
                          let w__132 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__131 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__131) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__132 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__135 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                let w__134 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__134 == 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__135 : Bool)
                          then
                            (do
                              let w__138 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__137 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__137) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__138 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__139 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (SPMCNTENSET_EL0_read
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__139)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__140 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64
                    (SPMCNTENSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__140)))))
              else (pure (())))))


end ArmFull.Functions
