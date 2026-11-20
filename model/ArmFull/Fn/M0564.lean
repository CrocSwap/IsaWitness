module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0227
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
def COSP_RCTX_SysOpsWrite_575f6b74afb13f3b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_COSPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_COSPRCTX w__4)
  let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool
        )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE
                                        w__16)) != 0b11#2) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (IsFeatureImplemented FEAT_FGT))
                       else (pure false)) : Bool)
                  then
                    (do
                      (pure ((← do
                            let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                            (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                  else (pure false)) && ((__HFGITR_EL2_COSPRCTX == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
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
                          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__29 RestrictType_Other)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__31 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__31 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__35 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__35) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_COSPRCTX == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__38 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__39 RestrictType_Other))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_RestrictPrediction w__40 RestrictType_Other))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__41 RestrictType_Other))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPP_RCTX_SysOpsWrite_40a73711d28892b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_CPPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_CPPRCTX w__4)
  let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool
        )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE
                                        w__16)) != 0b11#2) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (IsFeatureImplemented FEAT_FGT))
                       else (pure false)) : Bool)
                  then
                    (do
                      (pure ((← do
                            let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                            (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                  else (pure false)) && ((__HFGITR_EL2_CPPRCTX == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
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
                          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__29 RestrictType_CachePrefetch)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__31 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__31 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__35 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__35) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_CPPRCTX == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__38 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__39 RestrictType_CachePrefetch))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_RestrictPrediction w__40 RestrictType_CachePrefetch))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__41 RestrictType_CachePrefetch))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DVP_RCTX_SysOpsWrite_a4d7cddd32aa439c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DVPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_DVPRCTX w__4)
  let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool
        )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE
                                        w__16)) != 0b11#2) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (IsFeatureImplemented FEAT_FGT))
                       else (pure false)) : Bool)
                  then
                    (do
                      (pure ((← do
                            let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                            (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                  else (pure false)) && ((__HFGITR_EL2_DVPRCTX == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
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
                          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__29 RestrictType_DataValue)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__31 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__31 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__35 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__35) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DVPRCTX == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__38 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__39 RestrictType_DataValue))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_RestrictPrediction w__40 RestrictType_DataValue))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_RestrictPrediction w__41 RestrictType_DataValue))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE1IS_SysOpsWrite_03d7588893774850 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
              let w__4 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__4 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__5 Regime_EL10 Shareability_ISH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      (AArch64_TLBI_ALL w__6 Regime_EL10 Shareability_ISH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE1IS_SysOpsWrite_549e403ce92161b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              (AArch64_TLBI_ALL w__4 Regime_EL10 Shareability_ISH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__5 Regime_EL10 Shareability_ISH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE1OS_SysOpsWrite_614f5311238ca5e2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
              let w__4 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__4 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__5 Regime_EL10 Shareability_OSH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      (AArch64_TLBI_ALL w__6 Regime_EL10 Shareability_OSH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE1OS_SysOpsWrite_a4cd3a06ce23d819 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              (AArch64_TLBI_ALL w__4 Regime_EL10 Shareability_OSH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__5 Regime_EL10 Shareability_OSH TLBI_AllAttr))
              else (pure (())))))


end ArmFull.Functions
