import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0038
import ArmFull.Fn.M0041
import ArmFull.Fn.M0047
import ArmFull.Fn.M0051
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0063
import ArmFull.Fn.M0071
import ArmFull.Fn.M0073
import ArmFull.Fn.M0080
import ArmFull.Fn.M0092
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0164
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0186
import ArmFull.Fn.M0192
import ArmFull.Fn.M0199
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260
import ArmFull.Fn.M0924
import ArmFull.Fn.M0925
import ArmFull.Fn.M0926

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
def DC_IGDSW_SysOpsWrite_ad0a1d536c426f1f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCISW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCISW w__3)
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
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCISW == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_IGDVAC_SysOpsWrite_2b2dc8b1efa4218a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCIVAC : (BitVec 1) := (_get_HFGITR_EL2_Type_DCIVAC w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCIVAC == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data_Tag CacheOp_Invalidate CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_IGSW_SysOpsWrite_b40e0b982eab4603 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCISW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCISW w__3)
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
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCISW == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Tag CacheOp_Invalidate CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_IGVAC_SysOpsWrite_79e5a655957681f5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCIVAC : (BitVec 1) := (_get_HFGITR_EL2_Type_DCIVAC w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCIVAC == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Tag CacheOp_Invalidate CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_ISW_SysOpsWrite_d415f7441de61c87 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCISW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCISW w__3)
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
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCISW == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data CacheOp_Invalidate CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_IVAC_SysOpsWrite_9a59a62370daa1c9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCIVAC : (BitVec 1) := (_get_HFGITR_EL2_Type_DCIVAC w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCIVAC == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Data CacheOp_Invalidate CacheOpScope_PoC))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Data CacheOp_Invalidate CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data CacheOp_Invalidate CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def IC_IVAU_SysOpsWrite_f40d5c6453a840a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPU : (BitVec 1) := (_get_HCR_EL2_Type_TPU w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TOCU : (BitVec 1) := (_get_HCR_EL2_Type_TOCU w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ICIVAU : (BitVec 1) := (_get_HFGITR_EL2_Type_ICIVAU w__6)
  let w__7 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
        (pure ((← do
              let w__11 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__11) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
      if (w__12 : Bool)
      then
        (do
          let w__14 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE w__17)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
          if (w__19 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__24 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__21) +++ (_get_HCR_EL2_Type_TGE w__22)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TOCU == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                                 w__27)) != 0b11#2) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ICIVAU == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__34) +++ (_get_HCR_EL2_Type_TGE
                                          w__35)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_IC__1 w__38 CacheOpScope_PoU)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
          if (w__40 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__42 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TOCU == 1#1) : Bool))) ) : SailM Bool )
              if (w__42 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__47 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ICIVAU == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__47 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_IC__1 w__48 CacheOpScope_PoU)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_IC__1 w__49 CacheOpScope_PoU))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_IC__1 w__50 CacheOpScope_PoU))
              else (pure (())))))


/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegRead__1 (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2900) 2) ) : SailM (BitVec 2) )
  let index ← (( do (undefined_int_at (← occLabel 2901) ()) ) : SailM Int )
  let n ← (( do (undefined_int_at (← occLabel 2902) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (_, __tup_1) ← (( do (ELFromM32 w__0.M) ) : SailM (Bool × (BitVec 2)) )
  let el : (BitVec 2) := __tup_1
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let opc2 : (BitVec 3) :=
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && ((opc2 == 0b100#3) || (opc2 == 0b111#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
    then 0b000#3
    else opc2
  if ((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1101#4)) : Bool)
  then
    (do
      let n : Int :=
        (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access CRm 0)])) +++ opc2))
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b011#3) : Bool)
      then
        (do
          let w__1 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC w__1))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else (pure (()))
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b111#3) : Bool)
      then
        (do
          let w__2 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC w__2))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else (pure (())))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               CRm 3 2)) == 0b10#2) || ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb CRm
               3 2)) == 0b11#2))) && ((Sail.BitVec.castWidth (m := 5) ((Sail.BitVec.extractLsb CRm 1
             0) +++ (Sail.BitVec.extractLsb opc2 2 0))) != 0b11111#5)) : Bool)
  then
    (do
      let w__18 ← (( do
        if ((← do
             let w__3 ← (( do (GetNumEventCounters ()) ) : SailM Int )
             (pure ((((BitVec.toNat
                   ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__3 -i 1)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__5.EL == EL1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         if ((← do
                              let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__6.EL == EL0) : Bool)))) : Bool)
                         then
                           (do
                             if ((← do
                                  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb CRm
                                         3 2)) == 0b10#2) : Bool) : Bool)
                                  then
                                    (do
                                      let w__7 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64)
                                        )
                                      let w__8 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64)
                                        )
                                      (pure (((((_get_PMUSERENR_EL0_Type_ER w__7) +++ (_get_PMUSERENR_EL0_Type_EN
                                              w__8)) != 0b00#2) : Bool))))
                                  else (pure false)) : Bool)
                             then (pure true)
                             else
                               (do
                                 if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb CRm 3
                                        2)) == 0b11#2) : Bool) : Bool)
                                 then
                                   (do
                                     let w__10 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64)
                                       )
                                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__10) == 1#1) : Bool))))
                                 else (pure false)))
                         else (pure false)))
                 else (pure false)) : Bool)
            then
              (do
                let w__16 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat
                      ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__16 -i 1)) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__18 : Bool)
      then
        (do
          let w__19 ← (( do (GetNumEventCounters ()) ) : SailM Int )
          if (((BitVec.toNat
                 ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__19 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure (())))
  else (pure (()))
  let w__22 ← (( do
    if (((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3))) : Bool) : Bool)
    then
      (do
        let w__21 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSELR_EL0_Type_SEL w__21) != 0b11111#5) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__40 ← (( do
        if ((← do
             let w__23 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
             let w__24 ← (( do (GetNumEventCounters ()) ) : SailM Int )
             (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__23)) >b (w__24 -i 1)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__26.EL == EL1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         if ((← do
                              let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__27.EL == EL0) : Bool)))) : Bool)
                         then
                           (do
                             if ((← do
                                  if (((opc2 == 0b010#3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__28 ← (( do readReg PMUSERENR_EL0 ) : SailM
                                        (BitVec 64) )
                                      let w__29 ← (( do readReg PMUSERENR_EL0 ) : SailM
                                        (BitVec 64) )
                                      (pure (((((_get_PMUSERENR_EL0_Type_ER w__28) +++ (_get_PMUSERENR_EL0_Type_EN
                                              w__29)) != 0b00#2) : Bool))))
                                  else (pure false)) : Bool)
                             then (pure true)
                             else
                               (do
                                 if (((opc2 == 0b001#3) : Bool) : Bool)
                                 then
                                   (do
                                     let w__31 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64)
                                       )
                                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__31) == 1#1) : Bool))))
                                 else (pure false)))
                         else (pure false)))
                 else (pure false)) : Bool)
            then
              (do
                let w__37 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                let w__38 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__37)) >b (w__38 -i 1)) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__40 : Bool)
      then
        (do
          let w__41 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
          let w__42 ← (( do (GetNumEventCounters ()) ) : SailM Int )
          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__41)) >b (w__42 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__43 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              if (w__43 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure (())))
  else (pure (()))
  let temp ← (( do (R_read t) ) : SailM (BitVec 32) )
  (AArch32_AutoGen_SysRegRead32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
  then
    (do
      let w__44 ← (( do (PMUCounterMask ()) ) : SailM (BitVec 64) )
      let mask : (BitVec 32) := (Sail.BitVec.extractLsb w__44 31 0)
      let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (R_set t (w__45 &&& mask)))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3))) : Bool)
  then
    (do
      if ((opc2 == 0b001#3) : Bool)
      then
        (do
          let w__46 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
          let pmselr : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__46))
          let w__56 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__48 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__48.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__49 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__49.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__52 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_PMSELR_Type_SEL w__52) != 0b11111#5) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__54 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                let w__55 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__54)) >b (w__55 -i 1)) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__56 : Bool)
          then
            (do
              let w__57 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
              let w__58 ← (( do (GetNumEventCounters ()) ) : SailM Int )
              if (((BitVec.toNat (_get_PMSELR_Type_SEL w__57)) >b (w__58 -i 1)) : Bool)
              then
                (do
                  (R_set t temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  let w__59 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  if (w__59 : Bool)
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
          else
            (do
              if ((pmselr == 31) : Bool)
              then
                (do
                  let w__60 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__60))
              else
                (do
                  let w__61 ← (( do (PMEVTYPER_read (Sail.Int.toNatChecked (pmselr))) ) : SailM
                    (BitVec 32) )
                  (R_set t w__61))))
      else (pure (()))
      if ((opc2 == 0b010#3) : Bool)
      then
        (do
          let w__72 ← (( do
            if ((← do
                 let w__62 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                 let w__63 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                 (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__62)) >b (w__63 -i 1)) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         if ((← do
                              let w__65 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__65.EL == EL0) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__66 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__66.EL == EL1) : Bool)))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__69 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                    let w__70 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                    (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__69)) >b (w__70 -i 1)) : Bool))))
                else (pure false)) ) : SailM Bool )
          if (w__72 : Bool)
          then
            (do
              let w__73 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
              let w__74 ← (( do (GetNumEventCounters ()) ) : SailM Int )
              if (((BitVec.toNat (_get_PMSELR_Type_SEL w__73)) >b (w__74 -i 1)) : Bool)
              then
                (do
                  (R_set t temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  let w__75 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  if (w__75 : Bool)
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
          else
            (do
              let w__76 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
              let pmselr : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__76))
              ArmFull.assert (pmselr <b 31) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:1058.34-1058.35"
              let w__77 ← (( do (PMEVCNTR_read (Sail.Int.toNatChecked (pmselr))) ) : SailM
                (BitVec 32) )
              (R_set t (Sail.BitVec.extractLsb w__77 31 0))))
      else (pure (())))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      let w__78 ← (( do (R_read t) ) : SailM (BitVec 32) )
      let w__79 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
      (R_set t (Sail.BitVec.updateSubrange w__78 15 11 (integer_subrange w__79 4 0))))
  else (pure (()))
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             CRm 3 2)) == 0b10#2) || (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb CRm 3
               2)) == 0b11#2) && ((Sail.BitVec.castWidth (m := 5) ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb
                 opc2 2 0))) != 0b11111#5)))) : Bool)
  then
    (do
      let w__88 ← (( do
        if ((← do
             let w__80 ← (( do (GetNumEventCounters ()) ) : SailM Int )
             (pure ((((BitVec.toNat
                   ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__80 -i 1)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__82 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__82.EL == EL0) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__83 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__83.EL == EL1) : Bool)))))
                 else (pure false)) : Bool)
            then
              (do
                let w__86 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat
                      ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__86 -i 1)) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__88 : Bool)
      then
        (do
          let w__89 ← (( do (GetNumEventCounters ()) ) : SailM Int )
          if (((BitVec.toNat
                 ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__89 -i 1)) : Bool)
          then
            (do
              (R_set t temp)
              sailThrow ((Error_Undefined ())))
          else
            (do
              let w__90 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              if (w__90 : Bool)
              then
                (do
                  (R_set t temp)
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (R_set t temp)
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure (())))
  else (pure (()))
  if (((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) : Bool)
  then
    (do
      if ((CRm == 0b1000#4) : Bool)
      then
        (do
          let w__91 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (R_set t (Sail.BitVec.updateSubrange w__91 7 0 0b11111111#8)))
      else (pure (()))
      if ((CRm == 0b1001#4) : Bool)
      then
        (do
          let w__92 ← (( do (R_read t) ) : SailM (BitVec 32) )
          let w__93 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
          (R_set t (Sail.BitVec.updateSubrange w__92 7 0 (Sail.BitVec.extractLsb w__93 7 0))))
      else (pure (())))
  else
    (do
      if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b010#3)) && (CRn == 0b0000#4)) && (CRm == 0b0010#4)) : Bool)
      then
        (do
          let w__94 ← (( do (R_read t) ) : SailM (BitVec 32) )
          let w__95 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
          let w__96 : (BitVec 1) :=
            if ((BEq.beq w__95 SS_NonSecure) : Bool)
            then 1#1
            else 0#1
          (R_set t (Sail.BitVec.updateSubrange w__94 18 18 w__96))
          if ((HaveEL EL3) : Bool)
          then
            (do
              let w__99 ← (( do
                if ((← do
                     (ELUsingAArch32 EL3)) : Bool)
                then
                  (do
                    let w__98 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                    (pure ((((_get_SDCR_Type_SPME w__98) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__99 : Bool)
              then
                (do
                  let w__100 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (R_set t (Sail.BitVec.updateSubrange w__100 17 17 0#1)))
              else
                (do
                  let w__103 ← (( do
                    if ((← do
                         let w__101 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__101) : Bool)))) : Bool)
                    then
                      (do
                        let w__102 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_MDCR_EL3_Type_SPME w__102) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__103 : Bool)
                  then
                    (do
                      let w__104 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (R_set t (Sail.BitVec.updateSubrange w__104 17 17 0#1)))
                  else
                    (do
                      let w__105 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (R_set t (Sail.BitVec.updateSubrange w__105 17 17 1#1)))))
          else (pure (())))
      else
        (do
          if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1100#4)) && (CRm == 0b0001#4)) : Bool)
          then
            (do
              let w__106 ← (( do (getISR ()) ) : SailM (BitVec 32) )
              (R_set t w__106))
          else
            (do
              if ((((((cp_num == 15) && (opc1 == 0b001#3)) && ((opc2 == 0b000#3) || (opc2 == 0b010#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
              then
                (do
                  if ((opc2 == 0b000#3) : Bool)
                  then
                    (do
                      let w__107 ← (( do (CSSELR_read ()) ) : SailM (BitVec 32) )
                      let w__108 ← (( do (CacheConfigRead (Sail.BitVec.extractLsb w__107 3 0)) ) :
                        SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb w__108 31 0)))
                  else
                    (do
                      let w__109 ← (( do (CSSELR_read ()) ) : SailM (BitVec 32) )
                      let w__110 ← (( do (CacheConfigRead (Sail.BitVec.extractLsb w__109 3 0)) ) :
                        SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb w__110 63 32))))
              else
                (do
                  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0101#4)) && (CRm == 0b0100#4)) && ((opc2 == 0b000#3) || (opc2 == 0b100#3))) : Bool)
                  then
                    (do
                      let w__114 ← (( do
                        if ((← do
                             let w__111 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32) )
                             (pure ((((BitVec.toNat (_get_ERRIDR_Type_NUM w__111)) == (BitVec.toNat
                                   0x0#4)) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__112 ← (( do (ERRSELR_read ()) ) : SailM (BitVec 32) )
                            let w__113 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((BitVec.toNat (_get_ERRSELR_Type_SEL w__112)) ≥b (BitVec.toNat
                                  (_get_ERRIDR_Type_NUM w__113))) : Bool)))) ) : SailM Bool )
                      if (w__114 : Bool)
                      then
                        (do
                          (R_set t (Zeros (n := 32))))
                      else
                        (do
                          let w__115 ← (( do (ERRSELR_read ()) ) : SailM (BitVec 32) )
                          let index : Int := (BitVec.toNat (_get_ERRSELR_Type_SEL w__115))
                          if ((opc2 == 0b000#3) : Bool)
                          then
                            (do
                              ArmFull.assert ((0 ≤b index) && (index <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:1125.61-1125.62"
                              let w__116 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
                              (R_set t
                                (Sail.BitVec.extractLsb
                                  (GetElem?.getElem! w__116 (Sail.Int.toNatChecked (index))) 31 0)))
                          else
                            (do
                              ArmFull.assert ((0 ≤b index) && (index <b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:1128.61-1128.62"
                              let w__117 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
                              (R_set t
                                (Sail.BitVec.extractLsb
                                  (GetElem?.getElem! w__117 (Sail.Int.toNatChecked (index))) 63 32)))))
                  else (pure (()))
                  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (CRm == 0b0101#4)) && (opc2 == 0b000#3)) : Bool)
                  then
                    (do
                      let w__118 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
                      (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull w__118 0#1))
                      let w__119 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
                      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__119 30 30 0#1)
                      let w__120 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                      (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull w__120 0#1))
                      let w__121 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                      (EDSCR_write (_update_EDSCR_Type_RXfull w__121 0#1)))
                  else (pure (()))
                  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) && (opc2 == 0b010#3)) : Bool)
                  then
                    (do
                      let w__127 ← (( do
                        if ((← do
                             if ((← do
                                  (pure ((← do
                                        let w__122 ← (( do (CurrentSecurityState ()) ) : SailM
                                          SecurityState )
                                        (pure (((BEq.beq w__122 SS_NonSecure) : Bool)))) && ((HaveEL
                                        EL3) : Bool)))) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL3))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__126 ← (( do readReg NSACR ) : SailM (BitVec 32) )
                            (pure ((((_get_NSACR_Type_cp10 w__126) == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__127 : Bool)
                      then
                        (do
                          let w__128 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (R_set t (Sail.BitVec.updateSubrange w__128 23 20 0b0000#4)))
                      else (pure (())))
                  else (pure (()))))))


end ArmFull.Functions
