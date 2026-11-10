import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0058
import ArmFull.Fn.M0067
import ArmFull.Fn.M0070
import ArmFull.Fn.M0071
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073
import ArmFull.Fn.M0075
import ArmFull.Fn.M0079
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0200
import ArmFull.Fn.M0201
import ArmFull.Fn.M0254

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
def ICC_AP1R_EL1_SysRegWrite_58ad13edd90bb69b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
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
                          let w__19 ← (( do readReg ICV_AP1R_EL1 ) : SailM (Vector (BitVec 64) 4)
                            )
                          let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICV_AP1R_EL1 (vectorUpdate w__19 0 (Mk_ICV_AP1R_EL1_Type w__20)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              let w__22 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__22 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if ((HaveEL EL3) : Bool)
                              then
                                (do
                                  if ((__SCR_EL3_NS == 0#1) : Bool)
                                  then
                                    (do
                                      let w__23 ← (( do readReg ICC_AP1R_EL1_S ) : SailM
                                        (Vector (BitVec 64) 4) )
                                      let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg ICC_AP1R_EL1_S (vectorUpdate w__23 0
                                        (Mk_ICC_AP1R_EL1_Type w__24)))
                                  else
                                    (do
                                      let w__25 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM
                                        (Vector (BitVec 64) 4) )
                                      let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg ICC_AP1R_EL1_NS (vectorUpdate w__25 0
                                        (Mk_ICC_AP1R_EL1_Type w__26))))
                              else
                                (do
                                  let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (ICC_AP1R_EL1_set 0 (Mk_ICC_AP1R_EL1_Type w__27)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_IRQ == 1#1)) : Bool)
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
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__36 ← (( do readReg ICC_AP1R_EL1_S ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_AP1R_EL1_S (vectorUpdate w__36 0
                                    (Mk_ICC_AP1R_EL1_Type w__37)))
                              else
                                (do
                                  let w__38 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_AP1R_EL1_NS (vectorUpdate w__38 0
                                    (Mk_ICC_AP1R_EL1_Type w__39))))
                          else
                            (do
                              let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (ICC_AP1R_EL1_set 0 (Mk_ICC_AP1R_EL1_Type w__40)))))))
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
                          let w__41 ← (( do readReg ICC_AP1R_EL1_S ) : SailM
                            (Vector (BitVec 64) 4) )
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_AP1R_EL1_S (vectorUpdate w__41 0 (Mk_ICC_AP1R_EL1_Type w__42)))
                      else
                        (do
                          let w__43 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM
                            (Vector (BitVec 64) 4) )
                          let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_AP1R_EL1_NS (vectorUpdate w__43 0
                            (Mk_ICC_AP1R_EL1_Type w__44)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_ASGI1R_EL1_SysRegWrite_588d10b57224783c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__15 ← (( do
            if ((← do
                 if ((← do
                      (pure ((← do
                            (pure ((← do
                                  (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__13) +++ (_get_SCR_EL3_Type_FIQ w__14)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__19 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__21 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__24 ← (( do
                                if (((HaveEL EL3) : Bool) : Bool)
                                then
                                  (do
                                    let w__22 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__22) +++ (_get_SCR_EL3_Type_FIQ
                                            w__23)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__24 : Bool)
                              then
                                (do
                                  let w__26 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__26 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type w__27))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__35 ← (( do
                if ((← do
                     if ((← do
                          (pure ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__33 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__34 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__33) +++ (_get_SCR_EL3_Type_FIQ w__34)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__35 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__38 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            let w__36 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__37 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__36) +++ (_get_SCR_EL3_Type_FIQ w__37)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__38 : Bool)
                      then
                        (do
                          let w__40 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__40 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type w__41)))))
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
                      let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_ASGI1R_EL1 (Mk_ICC_ASGI1R_EL1_Type w__42)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_BPR0_EL1_SysRegWrite_4ea118667d9d50cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__13 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__17 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICV_BPR0_EL1 (Mk_ICV_BPR0_EL1_Type w__18))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              let w__20 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__20 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type w__21)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                      then
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__29 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type w__30)))))
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
                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_BPR0_EL1 (Mk_ICC_BPR0_EL1_Type w__31)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_CTLR_EL1_SysRegWrite_6b2222909cfe4181 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__16 ← (( do
            if ((← do
                 if ((← do
                      (pure ((← do
                            (pure ((← do
                                  (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__14) +++ (_get_SCR_EL3_Type_FIQ w__15)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
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
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICV_CTLR_EL1 (Mk_ICV_CTLR_EL1_Type w__21))
                      else
                        (do
                          let w__23 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICV_CTLR_EL1 (Mk_ICV_CTLR_EL1_Type w__24))
                          else
                            (do
                              let w__27 ← (( do
                                if (((HaveEL EL3) : Bool) : Bool)
                                then
                                  (do
                                    let w__25 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__25) +++ (_get_SCR_EL3_Type_FIQ
                                            w__26)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__27 : Bool)
                              then
                                (do
                                  let w__29 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__29 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then
                                    (do
                                      if ((__SCR_EL3_NS == 0#1) : Bool)
                                      then
                                        (do
                                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type w__30))
                                      else
                                        (do
                                          let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type w__31)))
                                  else
                                    (do
                                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type w__32))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do
                if ((← do
                     if ((← do
                          (pure ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__38 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__39 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__38) +++ (_get_SCR_EL3_Type_FIQ w__39)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
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
                      let w__43 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            let w__41 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__42 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__41) +++ (_get_SCR_EL3_Type_FIQ w__42)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          let w__45 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__45 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type w__46))
                              else
                                (do
                                  let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type w__47)))
                          else
                            (do
                              let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type w__48)))))))
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
                          let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_CTLR_EL1_S (Mk_ICC_CTLR_EL1_Type w__49))
                      else
                        (do
                          let w__50 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_CTLR_EL1_NS (Mk_ICC_CTLR_EL1_Type w__50))))
              else (pure (())))))


end ArmFull.Functions
