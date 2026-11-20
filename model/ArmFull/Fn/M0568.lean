module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
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
def TLBI_RIPAS2E1IS_SysOpsWrite_f517d8205e0bc7df (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1OS_SysOpsWrite_2c91dee891ab3686 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_OSH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1OS_SysOpsWrite_ed6e64c76758f7a2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_RIPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Any TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RIPAS2 w__8 Regime_EL10 w__9 Shareability_OSH TLBILevel_Any
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1_SysOpsWrite_1f3af7628a95cec3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_RIPAS2 w__4 Regime_EL10 w__5 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RIPAS2 w__8 Regime_EL10 w__9 Shareability_NSH TLBILevel_Any
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2E1_SysOpsWrite_49a01b03635148d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_NSH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_NSH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1IS_SysOpsWrite_34cdbedbc256d566 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_RIPAS2 w__4 Regime_EL10 w__5 Shareability_ISH TLBILevel_Last
                TLBI_AllAttr w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RIPAS2 w__8 Regime_EL10 w__9 Shareability_ISH TLBILevel_Last
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1IS_SysOpsWrite_73eb52c0eda77b8c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Last
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_ISH
                            TLBILevel_Last TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1OS_SysOpsWrite_54085ab636364748 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_RIPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Last
                TLBI_AllAttr w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RIPAS2 w__8 Regime_EL10 w__9 Shareability_OSH TLBILevel_Last
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1OS_SysOpsWrite_d4ca3cdc19ea21bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Last
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_OSH
                            TLBILevel_Last TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1_SysOpsWrite_360bee3e5adad3b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RIPAS2 w__5 Regime_EL10 w__6 Shareability_NSH TLBILevel_Last
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RIPAS2 w__9 Regime_EL10 w__10 Shareability_NSH
                            TLBILevel_Last TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RIPAS2LE1_SysOpsWrite_643a317b5666a6f1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_RIPAS2 w__4 Regime_EL10 w__5 Shareability_NSH TLBILevel_Last
                TLBI_AllAttr w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RIPAS2 w__8 Regime_EL10 w__9 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAAE1IS_SysOpsWrite_18faceee87b47845 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAAE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAAE1IS w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
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
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (IsFeatureImplemented FEAT_FGT))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if ((← do
                                                 let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                 (pure (((! w__13) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__14 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__14) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__19 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIRVAAE1IS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVAA w__23 Regime_EL10 w__24 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__25)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE w__27)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVAA w__28 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__29))
                  else
                    (do
                      let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVAA w__30 Regime_EL10 w__31 Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__32)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__33) +++ (_get_HCR_EL2_Type_TGE w__34)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__35 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVAA w__35 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Any TLBI_ExcludeXS w__36))
                      else
                        (do
                          let w__37 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__38 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVAA w__37 Regime_EL10 w__38 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__39)))
                  else (pure (()))))))


end ArmFull.Functions
