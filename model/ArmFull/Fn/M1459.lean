module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0065
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
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
def AMEVCNTVOFF1_EL2_SysRegWrite_f1ccc2e130743f64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 15) ) : SailM Bool )
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
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 15)) w__10))
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
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 15 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 15 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTVOFF1_EL2_SysRegWrite_fe51081bae489e73 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do (IsG1ActivityMonitorOffsetImplemented 7) ) : SailM Bool )
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
                  (NVMem_set ((BitVec.toNat 0xA80#12) +i (8 *i 7)) w__10))
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
                                  writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__35 7 w__36))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__37 ← (( do readReg AMEVCNTVOFF1_EL2 ) : SailM (Vector (BitVec 64) 16)
                        )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg AMEVCNTVOFF1_EL2 (vectorUpdate w__37 7 w__38))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def BRBCR_EL1_SysRegWrite_bacf32e45cccac33 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_SBRBE : (BitVec 2) := (_get_MDCR_EL3_Type_SBRBE w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__5)
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
              let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x8E0#12) w__11))
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
                  let w__21 ← (( do
                    (pure ((← do
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
                                else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__21 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__29 ← (( do
                        (pure ((← do
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
                                    else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                                  (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1
                                         0 0)) == (0#1 : (BitVec 1))) : Bool)
                                  then true
                                  else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__29 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                            ) : SailM Bool )
                          if (w__32 : Bool)
                          then
                            (do
                              let w__34 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__34 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__37 ← (( do
                                (pure ((← do
                                      (pure ((← do
                                            (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                          then true
                                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__37 : Bool)
                              then
                                (do
                                  let w__39 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__39 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type w__40))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__42) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type w__45))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRBCR_EL2_SysRegWrite_0f11184bdbd7fffd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_SBRBE : (BitVec 2) := (_get_MDCR_EL3_Type_SBRBE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_nBRBCTL : (BitVec 1) := (_get_HDFGWTR_EL2_Type_nBRBCTL w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do
            (pure ((← do
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
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__14 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
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
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__22 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_nBRBCTL == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          let w__34 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__34 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__37 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__2 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__37 : Bool)
                          then
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__39 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__44 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__41) +++ ((_get_HCR_EL2_Type_NV1
                                              w__42) +++ (_get_HCR_EL2_Type_NV w__43))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__44 : Bool)
                              then
                                (do
                                  let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (NVMem_set (BitVec.toNat 0x8E0#12) w__45))
                              else
                                (do
                                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type w__46))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__54 ← (( do
                (pure ((← do
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
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__54 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__62 ← (( do
                    (pure ((← do
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
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__62 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__65 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__65 : Bool)
                      then
                        (do
                          let w__67 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__67 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__70 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__70 : Bool)
                          then
                            (do
                              let w__72 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__72 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if ((__HCR_EL2_E2H == 1#1) : Bool)
                              then
                                (do
                                  let w__73 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg BRBCR_EL2 (Mk_BRBCR_EL2_Type w__73))
                              else
                                (do
                                  let w__74 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type w__74)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__75 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg BRBCR_EL1 (Mk_BRBCR_EL1_Type w__75))
              else (pure (())))))


end ArmFull.Functions
