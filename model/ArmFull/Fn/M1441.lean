module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
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
def MPAMVPM4_EL2_SysRegRead_2c47261ee8f811ec (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x960#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__14 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do readReg MPAMVPM4_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do readReg MPAMVPM4_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM5_EL2_SysRegRead_b3b860d951143744 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x968#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__14 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do readReg MPAMVPM5_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do readReg MPAMVPM5_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM6_EL2_SysRegRead_a456f2178fffbd2a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x970#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__14 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do readReg MPAMVPM6_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do readReg MPAMVPM6_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM7_EL2_SysRegRead_7f9fcda98e26326e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x978#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__14 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do readReg MPAMVPM7_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do readReg MPAMVPM7_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPMV_EL2_SysRegRead_3717c7fd58152b67 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x938#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__14 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAMVPMV_EL2 w__19))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAMVPMV_EL2 w__20)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PFAR_EL1_SysRegRead_648f6bc41e720a7a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__4) +++ ((_get_HCR_EL2_Type_NV1 w__5) +++ (_get_HCR_EL2_Type_NV
                          w__6))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x2D0#12)) ) : SailM (BitVec 64) )
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
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__11 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_PFAR_EL1 w__11)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__13 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__13) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_PFAR_EL1 w__16)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PFAR_EL1_SysRegRead_edf49fc5ee95c8c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__1)
  let w__2 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR2_EL2_nPFAR_EL1 : (BitVec 1) := (_get_HFGRTR2_EL2_Type_nPFAR_EL1 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           (IsFeatureImplemented FEAT_FGT2))
                       else (pure false)) : Bool)
                  then
                    (do
                      (HaveEL EL3))
                  else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (IsFeatureImplemented FEAT_FGT2))
                      else (pure false)) && ((__HFGRTR2_EL2_nPFAR_EL1 == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_NV2 w__15) +++ ((_get_HCR_EL2_Type_NV1 w__16) +++ (_get_HCR_EL2_Type_NV
                                  w__17))) == 0b111#3) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      let w__19 ← (( do (NVMem_read (BitVec.toNat 0x2D0#12)) ) : SailM (BitVec 64)
                        )
                      (X_set t 64 w__19))
                  else
                    (do
                      let w__20 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_PFAR_EL1 w__20))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__21 ← (( do readReg PFAR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_PFAR_EL2 w__21)))
              else
                (do
                  let w__22 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_PFAR_EL1 w__22))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_PFAR_EL1 w__23)))
              else (pure (())))))


end ArmFull.Functions
