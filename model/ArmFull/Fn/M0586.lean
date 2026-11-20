module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
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

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1OS_SysOpsWrite128_27f384221424e41f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_IPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Any TLBI_AllAttr
                (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_IPAS2 w__9 Regime_EL10 w__10 Shareability_OSH TLBILevel_Any
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1OS_SysOpsWrite128_db7744f725bc7991 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_IPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Any
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_IPAS2 w__10 Regime_EL10 w__11 Shareability_OSH
                            TLBILevel_Any TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1_SysOpsWrite128_769364ab2331c0c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_IPAS2 w__5 Regime_EL10 w__6 Shareability_NSH TLBILevel_Any
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_IPAS2 w__10 Regime_EL10 w__11 Shareability_NSH
                            TLBILevel_Any TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2E1_SysOpsWrite128_97574c637b9ec852 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_IPAS2 w__4 Regime_EL10 w__5 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_IPAS2 w__9 Regime_EL10 w__10 Shareability_NSH TLBILevel_Any
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1IS_SysOpsWrite128_0a969d7a2aebccaa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_IPAS2 w__4 Regime_EL10 w__5 Shareability_ISH TLBILevel_Last
                TLBI_AllAttr (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_IPAS2 w__9 Regime_EL10 w__10 Shareability_ISH TLBILevel_Last
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1IS_SysOpsWrite128_ddc96d61f96d402c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_IPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Last
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_IPAS2 w__10 Regime_EL10 w__11 Shareability_ISH
                            TLBILevel_Last TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1OS_SysOpsWrite128_84c03ae163aa7f64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_IPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Last
                TLBI_AllAttr (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_IPAS2 w__9 Regime_EL10 w__10 Shareability_OSH TLBILevel_Last
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1OS_SysOpsWrite128_eb8e7b685976ccc1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_IPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Last
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_IPAS2 w__10 Regime_EL10 w__11 Shareability_OSH
                            TLBILevel_Last TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1_SysOpsWrite128_0213d7545787eba6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_IPAS2 w__5 Regime_EL10 w__6 Shareability_NSH TLBILevel_Last
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_IPAS2 w__10 Regime_EL10 w__11 Shareability_NSH
                            TLBILevel_Last TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_IPAS2LE1_SysOpsWrite128_a67ad741d30f9316 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_IPAS2 w__4 Regime_EL10 w__5 Shareability_NSH TLBILevel_Last
                TLBI_AllAttr (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_IPAS2 w__9 Regime_EL10 w__10 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1IS_SysOpsWrite128_5606c3b58f00738a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
              let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBIP_RIPAS2 w__4 Regime_EL10 w__5 Shareability_ISH TLBILevel_Any
                TLBI_AllAttr (w__6 +++ w__7)))
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
                      let w__11 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RIPAS2 w__9 Regime_EL10 w__10 Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr (w__11 +++ w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RIPAS2E1IS_SysOpsWrite128_f1e0663ca68347ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RIPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Any
                    TLBI_ExcludeXS (w__7 +++ w__8)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__9) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__12 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RIPAS2 w__10 Regime_EL10 w__11 Shareability_ISH
                            TLBILevel_Any TLBI_ExcludeXS (w__12 +++ w__13))))
                  else (pure (()))))))


end ArmFull.Functions
