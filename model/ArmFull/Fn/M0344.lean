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
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0138
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
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

/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL1_SysRegRead_eb1de12df33d5c37 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__2)
  let w__3 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__6)
  let w__7 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__7)
  let w__8 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__8)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__17 ← (( do
            if ((← do
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
                 else (pure false)) : Bool)
            then
              (do
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__16 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__15) +++ (_get_SCR_EL3_Type_FIQ w__16)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          let w__22 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICV_CTLR_EL1 w__22)))
                      else
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__25 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ICV_CTLR_EL1 w__25)))
                          else
                            (do
                              let w__29 ← (( do
                                if ((← do
                                     (HaveEL EL3)) : Bool)
                                then
                                  (do
                                    let w__27 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__28 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__27) +++ (_get_SCR_EL3_Type_FIQ
                                            w__28)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__29 : Bool)
                              then
                                (do
                                  let w__31 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__31 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__32 ← (( do (HaveEL EL3) ) : SailM Bool )
                                  if (w__32 : Bool)
                                  then
                                    (do
                                      if ((__SCR_EL3_NS == 0#1) : Bool)
                                      then
                                        (do
                                          let w__33 ← (( do readReg ICC_CTLR_EL1_S ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64 (__get_ICC_CTLR_EL1_S w__33)))
                                      else
                                        (do
                                          let w__34 ← (( do readReg ICC_CTLR_EL1_NS ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64 (__get_ICC_CTLR_EL1_NS w__34))))
                                  else
                                    (do
                                      let w__35 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM
                                        (BitVec 64) )
                                      (X_set t 64 (__get_ICC_CTLR_EL1 w__35))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__44 ← (( do
                if ((← do
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
                     else (pure false)) : Bool)
                then
                  (do
                    let w__42 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__43 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__42) +++ (_get_SCR_EL3_Type_FIQ w__43)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__44 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__48 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            let w__46 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__47 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__46) +++ (_get_SCR_EL3_Type_FIQ w__47)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__48 : Bool)
                      then
                        (do
                          let w__50 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__50 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                          if (w__51 : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__52 ← (( do readReg ICC_CTLR_EL1_S ) : SailM (BitVec 64) )
                                  (X_set t 64 (__get_ICC_CTLR_EL1_S w__52)))
                              else
                                (do
                                  let w__53 ← (( do readReg ICC_CTLR_EL1_NS ) : SailM (BitVec 64)
                                    )
                                  (X_set t 64 (__get_ICC_CTLR_EL1_NS w__53))))
                          else
                            (do
                              let w__54 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ICC_CTLR_EL1 w__54)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then
                        (do
                          let w__55 ← (( do readReg ICC_CTLR_EL1_S ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICC_CTLR_EL1_S w__55)))
                      else
                        (do
                          let w__56 ← (( do readReg ICC_CTLR_EL1_NS ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICC_CTLR_EL1_NS w__56)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL3_SysRegRead_7a137fb26d669941 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__1)
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
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__2 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ICC_CTLR_EL3 w__2))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_HPPIR0_EL1_SysRegRead_03eb902d5ba703ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__18 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__18 : Bool)
                      then
                        (do
                          let w__19 ← (( do readReg ICV_HPPIR0_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICV_HPPIR0_EL1 w__19)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__21 : Bool)
                          then
                            (do
                              let w__23 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__23 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__24 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ICC_HPPIR0_EL1 w__24))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__31 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          let w__35 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__35 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__36 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICC_HPPIR0_EL1 w__36))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ICC_HPPIR0_EL1 w__37))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_HPPIR1_EL1_SysRegRead_49e183ca83eb8361 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_IRQ : (BitVec 1) := (_get_SCR_EL3_Type_IRQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL1 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL1 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL1 == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__18 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__18 : Bool)
                      then
                        (do
                          let w__19 ← (( do readReg ICV_HPPIR1_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICV_HPPIR1_EL1 w__19)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__21 : Bool)
                          then
                            (do
                              let w__23 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__23 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__24 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ICC_HPPIR1_EL1 w__24))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__31 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__33 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          let w__35 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__35 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__36 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICC_HPPIR1_EL1 w__36))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ICC_HPPIR1_EL1 w__37))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_IGRPEN0_EL1_SysRegRead_5872e0ee48947240 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_ICC_IGRPENn_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 w__5)
  let w__6 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__7)
  let w__8 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__8)
  let w__9 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__16 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__23 ← (( do
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
                                    let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGRTR_EL2_ICC_IGRPENn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ICV_IGRPEN0_EL1 w__28)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  let w__32 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__32 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__33 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64)
                                    )
                                  (X_set t 64 (__get_ICC_IGRPEN0_EL1 w__33)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__40 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          let w__44 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__44 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__45 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_ICC_IGRPEN0_EL1 w__45))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__46 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ICC_IGRPEN0_EL1 w__46))))
              else (pure (())))))


end ArmFull.Functions
