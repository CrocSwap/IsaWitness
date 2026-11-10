import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0153
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186

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
def TLBIP_VAE3IS_SysOpsWrite128_436ad5bd6c95d188 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3OS_SysOpsWrite128_0bd4cb2b344ca9a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3OS_SysOpsWrite128_7791c494d2ef59ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__2 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS (w__3 +++ w__4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3_SysOpsWrite128_2fd14fc00c09a0fd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__2 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS (w__3 +++ w__4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAE3_SysOpsWrite128_46537a58be020b54 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3IS_SysOpsWrite128_c86e34b8232f3903 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3IS_SysOpsWrite128_df84b0484150f9e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__2 Regime_EL3 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS (w__3 +++ w__4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3OS_SysOpsWrite128_e22bb7777364db32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3OS_SysOpsWrite128_f558b9d9636e92e8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__2 Regime_EL3 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS (w__3 +++ w__4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3_SysOpsWrite128_48fc2e32848138c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      let w__3 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VA w__2 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS (w__3 +++ w__4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VALE3_SysOpsWrite128_da83d084586f123a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  let w__2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VA w__1 Regime_EL3 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__2 +++ w__3)))
              else (pure (())))))


def getISR (_ : Unit) : SailM (BitVec 32) := do
  let fiq_nmi ← (( do (undefined_bool_at (← occLabel 2890) ()) ) : SailM Bool )
  let fiq_pending ← (( do (undefined_bool_at (← occLabel 2891) ()) ) : SailM Bool )
  let irq_nmi ← (( do (undefined_bool_at (← occLabel 2892) ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool_at (← occLabel 2893) ()) ) : SailM Bool )
  let value_name : (BitVec 32) := (Zeros (n := 32))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 8
      (Bit
        (if ((IsPhysicalSErrorPending ()) : Bool)
        then 1#1
        else 0#1)))
  let w__0 ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
  let (tup__0, tup__1) := (w__0 : (Bool × Bool))
  let irq_pending : Bool := tup__0
  let irq_nmi : Bool := tup__1
  let (tup__0, tup__1) := ((FIQPending ()) : (Bool × Bool))
  let fiq_pending : Bool := tup__0
  let fiq_nmi : Bool := tup__1
  let w__3 ← (( do
    if ((← do
         (HaveFeatNMI ())) : Bool)
    then
      (do
        let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let value_name : (BitVec 32) :=
    if (w__3 : Bool)
    then
      (let value_name : (BitVec 32) :=
        (BitVec.update value_name 10
          (Bit
            (if ((irq_pending && irq_nmi) : Bool)
            then 1#1
            else 0#1)))
      (BitVec.update value_name 9
        (Bit
          (if ((fiq_pending && fiq_nmi) : Bool)
          then 1#1
          else 0#1))))
    else value_name
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 7
      (Bit
        (if (irq_pending : Bool)
        then 1#1
        else 0#1)))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 6
      (Bit
        (if (fiq_pending : Bool)
        then 1#1
        else 0#1)))
  let w__8 ← (( do
    if ((← do
         if ((← do
              let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__4.EL == EL1) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__7) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      let w__13 ← (( do
        if ((← do
             if ((← do
                  (HaveFeatNMI ())) : Bool)
             then
               (do
                 let w__10 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                 (pure (((! w__10) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (IsHCRXEL2Enabled ()))
        else (pure false) ) : SailM Bool )
      let value_name ← (( do
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name ← (( do
              if ((((_get_HCR_EL2_Type_IMO w__14) &&& (_get_HCR_EL2_Type_VI w__15)) == 1#1) : Bool)
              then
                (do
                  let w__16 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                  let value_name :=
                    ((BitVec.update value_name 10 (Bit (_get_HCRX_EL2_Type_VINMI w__16))) : (BitVec 32))
                  (pure (value_name)))
              else (pure (value_name)) ) : SailM (BitVec 32) )
            let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            if ((((_get_HCR_EL2_Type_FMO w__17) &&& (_get_HCR_EL2_Type_VF w__18)) == 1#1) : Bool)
            then
              (do
                let w__19 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                let value_name :=
                  ((BitVec.update value_name 9 (Bit (_get_HCRX_EL2_Type_VFNMI w__19))) : (BitVec 32))
                (pure (value_name)))
            else (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_AMO w__20) == 1#1) : Bool)
        then
          (do
            let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name :=
              ((BitVec.update value_name 8
                (Bit
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access value_name 8)])) ||| (_get_HCR_EL2_Type_VSE
                      w__21)))) : (BitVec 32))
            (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_IMO w__22) == 1#1) : Bool)
        then
          (do
            let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name :=
              ((BitVec.update value_name 7 (Bit (_get_HCR_EL2_Type_VI w__23))) : (BitVec 32))
            (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      if (((_get_HCR_EL2_Type_FMO w__24) == 1#1) : Bool)
      then
        (do
          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
          let value_name :=
            ((BitVec.update value_name 6 (Bit (_get_HCR_EL2_Type_VF w__25))) : (BitVec 32))
          (pure (value_name)))
      else (pure (value_name)))
  else (pure (value_name))


def decode_aarch32_instrs_DMB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DMB_Op_A_txt option_name))
  else (pure (()))


def decode_aarch32_instrs_DMB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DMB_Op_A_txt option_name))
  else (pure (()))


def execute_aarch32_instrs_DSB_Op_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let nXS ← (( do (undefined_bool_at (← occLabel 3011) ()) ) : SailM Bool )
  let w__0 ← (( do (HaveFeatXS ()) ) : SailM Bool )
  let nXS ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       if ((← do
                            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__1.EL == EL0) : Bool)))) : Bool)
                       then (pure true)
                       else
                         (do
                           let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__2.EL == EL1) : Bool))))) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (IsHCRXEL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__8 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCRX_EL2_Type_FnXS w__8) == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let domain ← (( do (undefined_MBReqDomain (← occLabel 3012) ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes (← occLabel 3013) ()) ) : SailM MBReqTypes )
  let (domain, types) ← (( do
    match option_name with
    | 0b0001 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b0010 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b0011 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b0101 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b0110 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b0111 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b1001 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b1010 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b1011 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b1101 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b1110 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | _ =>
      (do
        let b__0 := option_name
        ArmFull.assert (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
          then true
          else false : Bool)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:3029.20-3029.21"
        let domain : MBReqDomain := MBReqDomain_FullSystem
        let types : MBReqTypes := MBReqTypes_All
        (pure ((domain, types)))) ) : SailM (MBReqDomain × MBReqTypes) )
  let types := types
  let w__14 ← (( do
    if ((← do
         if ((← do
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__10.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__11.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let domain ← (( do
    if (w__14 : Bool)
    then
      (do
        let w__15 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        let domain : MBReqDomain :=
          if (((_get_HCR_Type_BSU w__15) == 0b11#2) : Bool)
          then MBReqDomain_FullSystem
          else domain
        let w__17 ← (( do
          (pure ((← do
                let w__16 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__16) == 0b10#2) : Bool)))) && ((bne domain
                MBReqDomain_FullSystem) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__17 : Bool)
          then MBReqDomain_OuterShareable
          else domain
        let w__19 ← (( do
          (pure ((← do
                let w__18 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__18) == 0b01#2) : Bool)))) && ((BEq.beq domain
                MBReqDomain_Nonshareable) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__19 : Bool)
          then MBReqDomain_InnerShareable
          else domain
        (pure (domain)))
    else (pure (domain)) ) : SailM MBReqDomain )
  (DataSynchronizationBarrier domain types nXS)


end ArmFull.Functions
