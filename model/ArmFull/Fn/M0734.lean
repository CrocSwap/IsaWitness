import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0051
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0228
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
def COSPRCTX_SysRegWrite32_4f4dd157b3f4905c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_EnRCTX : (BitVec 1) := (_get_SCTLR_Type_EnRCTX w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__5)
  let w__6 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__6)
  let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__7)
  let w__8 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_COSPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_COSPRCTX w__8)
  let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__9)
  let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
        (pure ((← do
              if ((← do
                   let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then
                (do
                  let w__15 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__SCTLR_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                               (pure (((! w__33) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__42 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                    Bool )
                                                  (pure (((! w__44) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__46 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__47 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                     w__47)) != 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_COSPRCTX == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__59 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__54 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                           (pure (((! w__54) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__56 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__57 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__56) +++ (_get_HCR_EL2_Type_TGE
                                              w__57)) == 0b11#2) : Bool))))
                                  else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__59 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_RestrictPrediction w__60 RestrictType_Other))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__64 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__62 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__62) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__64 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__68 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__68 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__72 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__70 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__70) : Bool))))
                          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__72 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__73 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_RestrictPrediction w__73 RestrictType_Other)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__74 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_RestrictPrediction w__74 RestrictType_Other))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_RestrictPrediction w__75 RestrictType_Other))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CP15DMB_SysRegWrite32_d17f32fecbb5fdad (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_CP15BEN : (BitVec 1) := (_get_SCTLR_EL1_Type_CP15BEN w__1)
  let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_CP15BEN : (BitVec 1) := (_get_SCTLR_EL2_Type_CP15BEN w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_CP15BEN : (BitVec 1) := (_get_SCTLR_Type_CP15BEN w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__5)
  let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let __HSCTLR_CP15BEN : (BitVec 1) := (_get_HSCTLR_Type_CP15BEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__7) : Bool)))) : Bool)
              then
                (do
                  let w__11 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__11) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                           (pure (((! w__15) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__SCTLR_EL2_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__SCTLR_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__24) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                      w__27)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else (pure ((CP15DMB ()))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__37 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__41 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15DMB ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure ((CP15DMB ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15DMB ()))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CP15DSB_SysRegWrite32_e8d50e04da138ecc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_CP15BEN : (BitVec 1) := (_get_SCTLR_EL1_Type_CP15BEN w__1)
  let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_CP15BEN : (BitVec 1) := (_get_SCTLR_EL2_Type_CP15BEN w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_CP15BEN : (BitVec 1) := (_get_SCTLR_Type_CP15BEN w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__5)
  let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let __HSCTLR_CP15BEN : (BitVec 1) := (_get_HSCTLR_Type_CP15BEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__7) : Bool)))) : Bool)
              then
                (do
                  let w__11 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__11) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                           (pure (((! w__15) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__SCTLR_EL2_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__SCTLR_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__24) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                      w__27)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else (pure ((CP15DSB ()))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__37 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__41 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15DSB ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure ((CP15DSB ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15DSB ()))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CP15ISB_SysRegWrite32_b2e3d8ab360938e2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_CP15BEN : (BitVec 1) := (_get_SCTLR_EL1_Type_CP15BEN w__1)
  let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_CP15BEN : (BitVec 1) := (_get_SCTLR_EL2_Type_CP15BEN w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_CP15BEN : (BitVec 1) := (_get_SCTLR_Type_CP15BEN w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__5)
  let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let __HSCTLR_CP15BEN : (BitVec 1) := (_get_HSCTLR_Type_CP15BEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__7) : Bool)))) : Bool)
              then
                (do
                  let w__11 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__11) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                           (pure (((! w__15) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__SCTLR_EL2_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__SCTLR_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__24) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                      w__27)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else (pure ((CP15ISB ()))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__37 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__41 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15ISB ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure ((CP15ISB ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15ISB ()))))
              else (pure (())))))


end ArmFull.Functions
