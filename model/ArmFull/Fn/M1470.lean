module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0045
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
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
def MPAMHCR_EL2_SysRegWrite_f33f1b3939841d4d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x930#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMHCR_EL2 (Mk_MPAMHCR_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMHCR_EL2 (Mk_MPAMHCR_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM0_EL2_SysRegWrite_207148c31e856fe4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x940#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM0_EL2 (Mk_MPAMVPM0_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM0_EL2 (Mk_MPAMVPM0_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM1_EL2_SysRegWrite_b3375ea335a1385f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x948#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM1_EL2 (Mk_MPAMVPM1_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM1_EL2 (Mk_MPAMVPM1_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM2_EL2_SysRegWrite_8d820331d39fc415 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x950#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM2_EL2 (Mk_MPAMVPM2_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM2_EL2 (Mk_MPAMVPM2_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM3_EL2_SysRegWrite_021494dfdc0c0bfb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x958#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM3_EL2 (Mk_MPAMVPM3_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM3_EL2 (Mk_MPAMVPM3_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM4_EL2_SysRegWrite_b24395e23de9de27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x960#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM4_EL2 (Mk_MPAMVPM4_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM4_EL2 (Mk_MPAMVPM4_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMVPM5_EL2_SysRegWrite_6fb2fa1ed08eede5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x968#12) w__8))
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
                  let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM5_EL2 (Mk_MPAMVPM5_EL2_Type w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMVPM5_EL2 (Mk_MPAMVPM5_EL2_Type w__20))
              else (pure (())))))


end ArmFull.Functions
