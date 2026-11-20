module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
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
def AMEVCNTVOFF1_EL2_SysRegWrite_2ba85b85b5072821 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 10) ) : SailM Bool )
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
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ (_get_HCR_EL2_Type_NV w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 10)) w__10))
              else
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__19 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__26 ← (( do
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
                              else (pure false)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__32 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__32 : Bool)
                              then
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__34 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 10 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 10 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_386268cd3029fb99 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 11) ) : SailM Bool )
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
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ (_get_HCR_EL2_Type_NV w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 11)) w__10))
              else
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__19 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__26 ← (( do
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
                              else (pure false)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__32 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__32 : Bool)
                              then
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__34 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 11 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 11 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_55f6fd2dd91b0e50 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 6) ) : SailM Bool )
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
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ (_get_HCR_EL2_Type_NV w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 6)) w__10))
              else
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__19 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__26 ← (( do
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
                              else (pure false)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__32 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__32 : Bool)
                              then
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__34 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 6 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 6 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_715140b6e1ae357e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 14) ) : SailM Bool )
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
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ (_get_HCR_EL2_Type_NV w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 14)) w__10))
              else
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__19 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__26 ← (( do
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
                              else (pure false)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__32 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__32 : Bool)
                              then
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__34 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 14 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 14 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_894c1ceeabf341e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AMVOFFEN : (BitVec 1) := (_get_SCR_EL3_Type_AMVOFFEN w__4)
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 13) ) : SailM Bool )
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
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ (_get_HCR_EL2_Type_NV w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 13)) w__10))
              else
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__19 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__26 ← (( do
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
                              else (pure false)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_AMVOFFEN == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__32 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__32 : Bool)
                              then
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__34 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 13 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 13 w__38))
                  else (pure (()))))))


end ArmFull.Functions
