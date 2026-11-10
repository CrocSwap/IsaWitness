import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0079
import ArmFull.Fn.M0081
import ArmFull.Fn.M0092
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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
def CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PCTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PCTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PCTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PCTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let w__9 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_VHE)) : Bool)
    then
      (do
        let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_E2H w__8) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__10 : Int :=
    if (w__9 : Bool)
    then 10
    else 0
  let __CNTHCTL_EL2_EL1PCTEN : (BitVec 1) := (BitVec.slice w__6 (Sail.Int.toNatChecked (w__10)) 1)
  let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PCTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PCTEN w__11)
  let w__12 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHCTL_PL1PCTEN : (BitVec 1) := (_get_CNTHCTL_Type_PL1PCTEN w__12)
  let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__13)
  let w__14 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__14)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__21 ← (( do
        (pure ((← do
              if ((← do
                   let w__15 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__15) : Bool)))) : Bool)
              then
                (do
                  let w__19 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__19) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PCTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          let w__25 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__23) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__25 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
      else
        (do
          let w__27 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PCTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__27 : Bool)
          then
            (do
              let w__31 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__29) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__31 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__40 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__37) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__40 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__47 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__42) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__44) +++ (_get_HCR_EL2_Type_TGE
                                      w__45)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__47 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__49 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__49) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__51 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__52 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__51) +++ (_get_HCR_EL2_Type_TGE
                                          w__52)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PCTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCTEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__68 ← (( do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 if ((← do
                                                      if ((← do
                                                           (IsFeatureImplemented FEAT_ECV)) : Bool)
                                                      then
                                                        (do
                                                          (EL2Enabled ()))
                                                      else (pure false)) : Bool)
                                                 then
                                                   (do
                                                     let w__62 ← (( do (ELUsingAArch32 EL2) ) :
                                                       SailM Bool )
                                                     (pure (((! w__62) : Bool))))
                                                 else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__66 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__67 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__66) +++ (_get_HCR_EL2_Type_TGE
                                            w__67)) != 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__68 : Bool)
                              then
                                (do
                                  let w__69 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  let w__70 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) ← (( do (Split (w__69 - w__70) 32) ) :
                                    SailM ((BitVec 32) × (BitVec 32)) )
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__71 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) ← (( do (Split w__71 32) ) : SailM
                                    ((BitVec 32) × (BitVec 32)) )
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__75 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__73 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__73) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__75 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__79 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__CNTHCTL_PL1PCTEN == 0#1) : Bool))) ) : SailM Bool )
              if (w__79 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__86 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (IsFeatureImplemented FEAT_ECV)) : Bool)
                                     then
                                       (do
                                         (EL2Enabled ()))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__83 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                    (pure (((! w__83) : Bool))))
                                else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__86 : Bool)
                  then
                    (do
                      let w__87 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__88 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split (w__87 - w__88) 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__89 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split w__89 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__90 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) ← (( do (Split w__90 32) ) : SailM
                ((BitVec 32) × (BitVec 32)) )
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__91 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) ← (( do (Split w__91 32) ) : SailM
                    ((BitVec 32) × (BitVec 32)) )
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVCT_SysRegRead64_6e373436952b9ca9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VCTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VCTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0VCTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0VCTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VCTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VCTEN w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVCT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVCT w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__7) : Bool)))) : Bool)
              then
                (do
                  let w__11 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__11) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0VCTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__15) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0VCTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__19 : Bool)
          then
            (do
              let w__23 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__21) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__27 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                               (pure (((! w__29) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__31) +++ (_get_HCR_EL2_Type_TGE w__32)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL0VCTEN == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__41 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__36 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__36) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__38) +++ (_get_HCR_EL2_Type_TGE
                                      w__39)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1TVCT == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__48 ← (( do
                        if ((← do
                             if (((HaveEL EL2) : Bool) : Bool)
                             then
                               (do
                                 let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__42) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__44 ← (( do (EL2Enabled ()) ) : SailM Bool )
                                 (pure (((! w__44) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_E2H w__45) +++ (_get_HCR_EL2_Type_TGE
                                        w__46)) != 0b11#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__48 : Bool)
                      then
                        (do
                          let w__49 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__50 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) ← (( do (Split (w__49 - w__50) 32) ) : SailM
                            ((BitVec 32) × (BitVec 32)) )
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          let w__52 ← (( do
                            if (((HaveEL EL2) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL2))
                            else (pure false) ) : SailM Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              let w__53 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__54 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) ← (( do (Split (w__53 - w__54) 32) ) : SailM
                                ((BitVec 32) × (BitVec 32)) )
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__55 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) ← (( do (Split w__55 32) ) : SailM
                                ((BitVec 32) × (BitVec 32)) )
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__59 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__57 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__57) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1TVCT == 1#1) : Bool))) ) : SailM Bool )
          if (w__59 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__61 ← (( do
                if (((HaveEL EL2) : Bool) : Bool)
                then
                  (do
                    let w__60 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__60) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__61 : Bool)
              then
                (do
                  let w__62 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__63 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) ← (( do (Split (w__62 - w__63) 32) ) : SailM
                    ((BitVec 32) × (BitVec 32)) )
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let w__65 ← (( do
                    if (((HaveEL EL2) : Bool) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then
                    (do
                      let w__66 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__67 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split (w__66 - w__67) 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__68 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split w__68 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__69 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              let w__70 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) ← (( do (Split (w__69 - w__70) 32) ) : SailM
                ((BitVec 32) × (BitVec 32)) )
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((HaveEL EL2) : Bool)
                  then
                    (do
                      let w__71 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__72 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split (w__71 - w__72) 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__73 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) ← (( do (Split w__73 32) ) : SailM
                        ((BitVec 32) × (BitVec 32)) )
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


end ArmFull.Functions
