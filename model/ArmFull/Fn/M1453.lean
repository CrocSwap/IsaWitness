module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0138
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M1340 set_option backward.proofsInPublic true @[expose] public section

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
def VDISR_EL2_SysRegRead_354cfd34639eb7c6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x500#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VDISR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VDISR_EL2 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VMPIDR_EL2_SysRegRead_4d4e4e0bcb925136 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x050#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VMPIDR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (HaveEL EL2) ) : SailM Bool )
                  if ((! w__10) : Bool)
                  then
                    (do
                      let w__11 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_MPIDR_EL1 w__11)))
                  else
                    (do
                      let w__12 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_VMPIDR_EL2 w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VNCR_EL2_SysRegRead_fd49e25478d53eb1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x0B0#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VNCR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VNCR_EL2 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VPIDR_EL2_SysRegRead_c419b4414b36ba2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x088#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VPIDR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (HaveEL EL2) ) : SailM Bool )
                  if ((! w__10) : Bool)
                  then
                    (do
                      let w__11 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_MIDR_EL1 w__11)))
                  else
                    (do
                      let w__12 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_VPIDR_EL2 w__12))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VSESR_EL2_SysRegRead_dcbab774e333f499 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x508#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VSESR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VSESR_EL2 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VSTCR_EL2_SysRegRead_15cf4d2aac84d328 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__7 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  let w__8 ← (( do (NVMem_read (BitVec.toNat 0x048#12)) ) : SailM (BitVec 64) )
                  (X_set t 64 w__8))
              else
                (do
                  let w__10 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__11) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__12 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VSTCR_EL2 w__12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_VSTCR_EL2 w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VSTTBR_EL2_SysRegRead_5dcb8c3ead41869d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__7 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  let w__8 ← (( do (NVMem_read (BitVec.toNat 0x030#12)) ) : SailM (BitVec 64) )
                  (X_set t 64 w__8))
              else
                (do
                  let w__10 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__11) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__12 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VSTTBR_EL2 w__12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_VSTTBR_EL2 w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VTCR_EL2_SysRegRead_f801b4fb3334c4c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x040#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_VTCR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VTCR_EL2 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VTTBR_EL2_SysRegRead_1816600c5e2db377 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (NVMem_read (BitVec.toNat 0x020#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (X_set t 64 (Sail.BitVec.extractLsb (__get_VTTBR_EL2 w__9) 63 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  (X_set t 64 (Sail.BitVec.extractLsb (__get_VTTBR_EL2 w__10) 63 0)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ZCR_EL1_SysRegRead_ae33ffd6ee977eba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_ZEN : (BitVec 2) := (_get_CPTR_EL2_Type_ZEN w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ ((_get_HCR_EL2_Type_NV1 w__8) +++ (_get_HCR_EL2_Type_NV
                          w__9))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__11 ← (( do (NVMem_read (BitVec.toNat 0x1E0#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__11))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((let b__0 := __CPTR_EL2_ZEN
                         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool
                            )
                          if (w__22 : Bool)
                          then
                            (do
                              let w__24 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__24 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))))
                          else
                            (do
                              let w__25 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ZCR_EL1 w__25))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__27) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_EZ == 0#1) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          let w__30 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ZCR_EL1 w__30))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


end ArmFull.Functions
