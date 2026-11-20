module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0957 set_option backward.proofsInPublic true @[expose] public section

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
def DC_CGSW_SysOpsWrite_1f93959761278ed4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCSW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCSW w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TSW == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCSW == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Tag CacheOp_Clean CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__14 CacheType_Tag CacheOp_Clean CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__15 CacheType_Tag CacheOp_Clean CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGVAC_SysOpsWrite_c31db9a0c232aa17 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVAC : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVAC w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
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
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
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
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                            w__21)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE
                                      w__31)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__34 CacheType_Tag CacheOp_Clean CacheOpScope_PoC))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__36 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__36 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__43 ← (( do
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
                                let w__40 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__40) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__43 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__44 CacheType_Tag CacheOp_Clean CacheOpScope_PoC))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__45 CacheType_Tag CacheOp_Clean CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__46 CacheType_Tag CacheOp_Clean CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGVADP_SysOpsWrite_6e93030bf0a27352 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVADP : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVADP w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
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
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
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
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                            w__21)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVADP == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE
                                      w__31)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__34 CacheType_Tag CacheOp_Clean CacheOpScope_PoDP))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__36 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__36 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__43 ← (( do
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
                                let w__40 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__40) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVADP == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__43 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__44 CacheType_Tag CacheOp_Clean CacheOpScope_PoDP))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__45 CacheType_Tag CacheOp_Clean CacheOpScope_PoDP))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__46 CacheType_Tag CacheOp_Clean CacheOpScope_PoDP))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGVAP_SysOpsWrite_884677eb0934135e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVAP : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVAP w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
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
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
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
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                            w__21)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVAP == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE
                                      w__31)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__34 CacheType_Tag CacheOp_Clean CacheOpScope_PoP))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__36 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__36 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__43 ← (( do
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
                                let w__40 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__40) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCVAP == 1#1) : Bool))) ) : SailM Bool )
              if (w__43 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__44 CacheType_Tag CacheOp_Clean CacheOpScope_PoP))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__45 CacheType_Tag CacheOp_Clean CacheOpScope_PoP))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__46 CacheType_Tag CacheOp_Clean CacheOpScope_PoP))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CIGDPAE_SysOpsWrite_8bfd8283adbf50a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__1 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__2 CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoE)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__3 CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_PoE))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CIGDSW_SysOpsWrite_b520ae0cd5c0ff01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCISW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCISW w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TSW == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_DCCISW == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__14 CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__15 CacheType_Data_Tag CacheOp_CleanInvalidate CacheOpScope_SetWay))
              else (pure (())))))


end ArmFull.Functions
