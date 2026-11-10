import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0174
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185

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
def TLBI_ALLE3IS_SysOpsWrite_95e13b1ef487429e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_ISH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3IS_SysOpsWrite_f68dcd86f3998afd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_ISH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_7d60d9e9832a86fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_OSH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_f5180bd2c6904111 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_OSH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_154b769b60a9a83a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_NSH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_f67a5db4b11c6ca5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_NSH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_61186878beebdd00 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_e7bda4e5b52e0dd2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_ISH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_51cc3eac56f81d7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_OSH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_b68e938dbaed6553 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3_SysOpsWrite_9115183869722fc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


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


end ArmFull.Functions
