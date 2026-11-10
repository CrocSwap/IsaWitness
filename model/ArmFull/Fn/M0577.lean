import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0115
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0159
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0244
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255

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
def TLBIP_VALE2IS_SysOpsWrite128_678498d40a585a6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
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
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__5 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr (w__6 +++ w__7)))
              else
                (do
                  let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__9 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__8 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr (w__9 +++ w__10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__12 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Last TLBI_AllAttr (w__13 +++ w__14)))
                      else
                        (do
                          let w__15 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__16 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__15 Regime_EL2 VMID_NONE Shareability_ISH
                            TLBILevel_Last TLBI_AllAttr (w__16 +++ w__17)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2IS_SysOpsWrite128_78fde03af9aaffc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__6 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS (w__7 +++ w__8)))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__10 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__9 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS (w__10 +++ w__11))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__12 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__12) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__13 Regime_EL20 VMID_NONE Shareability_ISH
                                TLBILevel_Last TLBI_ExcludeXS (w__14 +++ w__15)))
                          else
                            (do
                              let w__16 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__17 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__16 Regime_EL2 VMID_NONE Shareability_ISH
                                TLBILevel_Last TLBI_ExcludeXS (w__17 +++ w__18)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2OS_SysOpsWrite128_843e0c96a4c62b9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
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
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__5 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr (w__6 +++ w__7)))
              else
                (do
                  let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__9 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__8 Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr (w__9 +++ w__10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__12 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBILevel_Last TLBI_AllAttr (w__13 +++ w__14)))
                      else
                        (do
                          let w__15 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__16 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__15 Regime_EL2 VMID_NONE Shareability_OSH
                            TLBILevel_Last TLBI_AllAttr (w__16 +++ w__17)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2OS_SysOpsWrite128_a461faf4d3b82a3e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__6 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS (w__7 +++ w__8)))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__10 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__9 Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS (w__10 +++ w__11))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__12 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__12) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__13 Regime_EL20 VMID_NONE Shareability_OSH
                                TLBILevel_Last TLBI_ExcludeXS (w__14 +++ w__15)))
                          else
                            (do
                              let w__16 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__17 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__16 Regime_EL2 VMID_NONE Shareability_OSH
                                TLBILevel_Last TLBI_ExcludeXS (w__17 +++ w__18)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2_SysOpsWrite128_9b47499d61569e08 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__6 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS (w__7 +++ w__8)))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__10 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__9 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS (w__10 +++ w__11))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__12 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__12) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__13 Regime_EL20 VMID_NONE Shareability_NSH
                                TLBILevel_Last TLBI_ExcludeXS (w__14 +++ w__15)))
                          else
                            (do
                              let w__16 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__17 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                              let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBIP_VA w__16 Regime_EL2 VMID_NONE Shareability_NSH
                                TLBILevel_Last TLBI_ExcludeXS (w__17 +++ w__18)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE2_SysOpsWrite128_ad7af3eba7e26934 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
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
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__5 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__6 +++ w__7)))
              else
                (do
                  let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__9 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__8 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__9 +++ w__10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__12 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr (w__13 +++ w__14)))
                      else
                        (do
                          let w__15 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__16 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VA w__15 Regime_EL2 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr (w__16 +++ w__17)))))
              else (pure (())))))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2908) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2909) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) := ((AddWithCarry w__0 imm32 w__1.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2910) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2911) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) := ((AddWithCarry w__2 shifted w__3.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_i_OpA_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2920) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2921) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__0 imm32 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2924) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2925) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__2 shifted 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_SP_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2936) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2937) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read 13) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__0 imm32 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


end ArmFull.Functions
