module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0184 set_option backward.proofsInPublic true @[expose] public section

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
def TLBI_RVAE3_SysOpsWrite_aa377993d94b4c2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3IS_SysOpsWrite_7257c0dcb24e4a80 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3IS_SysOpsWrite_879fb376d7b6807d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3OS_SysOpsWrite_ac643f4910daad7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3OS_SysOpsWrite_bdb9e7fcdda16e82 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3_SysOpsWrite_14a8b6cb081a1329 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE3_SysOpsWrite_c0f76daa7c4a5790 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3IS_SysOpsWrite_067b7469c1e1bb6d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3IS_SysOpsWrite_26beb941bc870811 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3OS_SysOpsWrite_1c55c5510bb06701 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3OS_SysOpsWrite_b1a90c282b7de961 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3_SysOpsWrite_41a4620adcceb248 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE3_SysOpsWrite_de8987d56f578140 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3IS_SysOpsWrite_4c94c8515b6e4dd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3IS_SysOpsWrite_dae432255a8b0524 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3OS_SysOpsWrite_767bde9c297cce04 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3OS_SysOpsWrite_af6269968bb4ec2c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3_SysOpsWrite_6432751b5694bad8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__1 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE3_SysOpsWrite_eb6afd5e3f195389 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__2 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS w__3))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3IS_SysOpsWrite128_46b2dc8d96c6ca59 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__1 Regime_EL3 w__2 Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr (w__3 +++ w__4)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3IS_SysOpsWrite128_b118fa02f013962a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__2 Regime_EL3 w__3 Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS (w__4 +++ w__5)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE3OS_SysOpsWrite128_2d1acd5b6076c150 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__1 Regime_EL3 w__2 Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr (w__3 +++ w__4)))
              else (pure (())))))


end ArmFull.Functions
