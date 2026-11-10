import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0046
import ArmFull.Fn.M0058
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0187
import ArmFull.Fn.M0209
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

/-- Type quantifiers: t : Int, t2 : Int -/
def S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EnIDCP128 : (BitVec 1) := (_get_SCR_EL3_Type_EnIDCP128 w__2)
  let w__3 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_TIDCP : (BitVec 1) := (_get_SCTLR_EL1_Type_TIDCP w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_TIDCP : (BitVec 1) := (_get_SCTLR_EL2_Type_TIDCP w__5)
  let w__6 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  let __SCTLR2_EL1_EnIDCP128 : (BitVec 1) := (_get_SCTLR2_EL1_Type_EnIDCP128 w__6)
  let w__7 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  let __SCTLR2_EL2_EnIDCP128 : (BitVec 1) := (_get_SCTLR2_EL2_Type_EnIDCP128 w__7)
  let w__8 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_EnIDCP128 : (BitVec 1) := (_get_HCRX_EL2_Type_EnIDCP128 w__8)
  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TIDCP : (BitVec 1) := (_get_HCR_EL2_Type_TIDCP w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__15 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
      if (w__15 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  let w__19 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__19) : Bool)))) && ((__SCTLR_EL1_TIDCP == 1#1) : Bool))) ) : SailM
            Bool )
          if (w__20 : Bool)
          then
            (do
              let w__22 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8))))
          else
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__24) +++ (_get_HCR_EL2_Type_TGE w__25)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__SCTLR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__34 ← (( do
                    if ((← do
                         let w__31 ← (( do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure (((((_get_HCR_EL2_Type_E2H w__29) +++ (_get_HCR_EL2_Type_TGE
                                       w__30)) == 0b11#2) : Bool))))
                           else (pure false) ) : SailM Bool )
                         (pure (((! w__31) : Bool)))) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__32 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                              (pure (((! w__32) : Bool)))) || ((__SCTLR2_EL1_EnIDCP128 == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__43 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__38) +++ (_get_HCR_EL2_Type_TGE
                                         w__39)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__41 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__41) : Bool)))) || ((__SCTLR2_EL2_EnIDCP128 == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__50 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__45) +++ (_get_HCR_EL2_Type_TGE
                                             w__46)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (pure ((← do
                                      let w__48 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                      (pure (((! w__48) : Bool)))) || ((__HCRX_EL2_EnIDCP128 == 0#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__50 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                              then
                                (do
                                  let w__52 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__52 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                              else
                                (do
                                  (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__58 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
          if (w__58 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__60 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
              if (w__60 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__64 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__62 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                              (pure (((! w__62) : Bool)))) || ((__HCRX_EL2_EnIDCP128 == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__64 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                      then
                        (do
                          let w__66 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__66 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__72 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
              if (w__72 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                  then
                    (do
                      let w__74 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__74 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
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
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__13 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__13 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__14 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__14 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__15 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegRead128_712360e50061655a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
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
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__13 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__13 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__14 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__14 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__15 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_EL1_SysRegWrite128_e67f3244d494abe6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_PAR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_PAR_EL1 w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_PAR_EL1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__20 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__18 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                              (pure (((! w__18) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__22 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__23 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) := (w__23, w__24)
                          let w__25 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          (PAR_EL1_write
                            (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__25 127 64 __tup_0)))
                          let w__26 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          (PAR_EL1_write
                            (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__26 63 0 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__32 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__32 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__34 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__35 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) := (w__35, w__36)
                      let w__37 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      (PAR_EL1_write
                        (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__37 127 64 __tup_0)))
                      let w__38 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      (PAR_EL1_write
                        (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__38 63 0 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) := (w__39, w__40)
                  let w__41 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__41 127 64 __tup_0)))
                  let w__42 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__42 63 0 __tup_1))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_RCWMASKEn : (BitVec 1) := (_get_SCR_EL3_Type_RCWMASKEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nRCWMASK_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nRCWMASK_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__18 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__23 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_nRCWMASK_EL1 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__27 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__25 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__25) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                          then
                            (do
                              let w__29 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__29 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
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
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                              else
                                (do
                                  let w__32 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                                  let w__33 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  let (tup__0, tup__1) :=
                                    ((w__32, w__33) : ((BitVec 64) × (BitVec 64)))
                                  let w__34 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__34 127 64
                                    tup__0)
                                  let w__35 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__35 63 0 tup__1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__47 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__47 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_RCWMASKEn == 0#1)) : Bool)
                      then
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__49 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              let w__51 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__51 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__52 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                              let w__53 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let (tup__0, tup__1) :=
                                ((w__52, w__53) : ((BitVec 64) × (BitVec 64)))
                              let w__54 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__54 127 64 tup__0)
                              let w__55 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__55 63 0 tup__1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__56 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__57 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let (tup__0, tup__1) := ((w__56, w__57) : ((BitVec 64) × (BitVec 64)))
                  let w__58 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__58 127 64 tup__0)
                  let w__59 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__59 63 0 tup__1))
              else (pure (())))))


end ArmFull.Functions
