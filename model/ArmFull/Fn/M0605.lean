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
import ArmFull.Fn.M0042
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0081
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0141
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0198
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

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegRead32_fdd1a67f3e306983 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__6)
  let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__7)
  let w__8 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__8)
  let w__9 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHCTL_PL1PCEN : (BitVec 1) := (_get_CNTHCTL_Type_PL1PCEN w__9)
  let w__10 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHPS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHPS_CTL_EL2_Type_ENABLE w__10)
  let w__11 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHP_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHP_CTL_EL2_Type_ENABLE w__11)
  let w__12 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__12)
  let w__13 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__13)
  let w__14 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
  let __CNTP_CTL_ENABLE : (BitVec 1) := (_get_CNTP_CTL_Type_ENABLE w__14)
  let w__15 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__15)
  let w__16 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
  let __CNTP_CTL_NS_ENABLE : (BitVec 1) := (_get_CNTP_CTL_Type_ENABLE w__16)
  let w__17 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
  let __CNTP_CTL_S_ENABLE : (BitVec 1) := (_get_CNTP_CTL_Type_ENABLE w__17)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__24 ← (( do
        (pure ((← do
              if ((← do
                   let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__18) : Bool)))) : Bool)
              then
                (do
                  let w__22 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE w__21)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__22) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__24 : Bool)
      then
        (do
          let w__28 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__26 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__26) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__28 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__30 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__30 : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__32) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__43 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__40) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__43 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__50 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__45 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__45) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__47) +++ (_get_HCR_EL2_Type_TGE
                                      w__48)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__50 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__57 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__52 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__52) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__55 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__54) +++ (_get_HCR_EL2_Type_TGE
                                          w__55)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__57 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__61 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__71 ← (( do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               if ((← do
                                                    (EL2Enabled ())) : Bool)
                                               then
                                                 (do
                                                   let w__63 ← (( do (ELUsingAArch32 EL2) ) :
                                                     SailM Bool )
                                                   (pure (((! w__63) : Bool))))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              let w__65 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              let w__66 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              (pure (((((_get_HCR_EL2_Type_E2H w__65) +++ (_get_HCR_EL2_Type_TGE
                                                      w__66)) == 0b11#2) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__68 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                         (pure ((((_get_SCR_EL3_Type_NS w__68) == 0#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_SEL2))
                                else (pure false) ) : SailM Bool )
                              if (w__71 : Bool)
                              then
                                (do
                                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                                  then
                                    (do
                                      let w__72 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32)
                                        )
                                      (R_set t w__72))
                                  else
                                    (do
                                      let w__73 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM
                                        (BitVec 64) )
                                      let w__74 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      (R_set t (Sail.BitVec.extractLsb (w__73 - w__74) 31 0))))
                              else
                                (do
                                  let w__82 ← (( do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__76 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__76) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__78 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__79 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__78) +++ (_get_HCR_EL2_Type_TGE
                                                     w__79)) == 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__81 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure ((((_get_SCR_EL3_Type_NS w__81) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__82 : Bool)
                                  then
                                    (do
                                      if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                                      then
                                        (do
                                          let w__83 ← (( do (__UNKNOWN_bits 32) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__83))
                                      else
                                        (do
                                          let w__84 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM
                                            (BitVec 64) )
                                          let w__85 ← (( do (PhysicalCountInt ()) ) : SailM
                                            (BitVec 64) )
                                          (R_set t (Sail.BitVec.extractLsb (w__84 - w__85) 31 0))))
                                  else
                                    (do
                                      let w__95 ← (( do
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
                                                             let w__89 ← (( do
                                                               (ELUsingAArch32 EL2) ) : SailM Bool )
                                                             (pure (((! w__89) : Bool))))
                                                         else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__93 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__94 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__93) +++ (_get_HCR_EL2_Type_TGE
                                                    w__94)) != 0b11#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__95 : Bool)
                                      then
                                        (do
                                          if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                                          then
                                            (do
                                              let w__96 ← (( do (__UNKNOWN_bits 32) ) : SailM
                                                (BitVec 32) )
                                              (R_set t w__96))
                                          else
                                            (do
                                              let w__97 ← (( do (CNTP_CVAL_read ()) ) : SailM
                                                (BitVec 64) )
                                              let w__98 ← (( do (PhysicalCountInt ()) ) : SailM
                                                (BitVec 64) )
                                              let w__99 ← (( do readReg CNTPOFF_EL2 ) : SailM
                                                (BitVec 64) )
                                              (R_set t
                                                (Sail.BitVec.extractLsb (w__97 - (w__98 - w__99)) 31
                                                  0))))
                                      else
                                        (do
                                          let w__101 ← (( do
                                            if (((HaveEL EL3) : Bool) : Bool)
                                            then
                                              (do
                                                (ELUsingAArch32 EL3))
                                            else (pure false) ) : SailM Bool )
                                          if (w__101 : Bool)
                                          then
                                            (do
                                              if ((__SCR_NS == 1#1) : Bool)
                                              then
                                                (do
                                                  if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                                                  then
                                                    (do
                                                      let w__102 ← (( do (__UNKNOWN_bits 32) ) :
                                                        SailM (BitVec 32) )
                                                      (R_set t w__102))
                                                  else
                                                    (do
                                                      let w__103 ← (( do (CNTP_CVAL_NS_read ()) )
                                                        : SailM (BitVec 64) )
                                                      let w__104 ← (( do (PhysicalCountInt ()) ) :
                                                        SailM (BitVec 64) )
                                                      (R_set t
                                                        (Sail.BitVec.extractLsb (w__103 - w__104) 31
                                                          0))))
                                              else
                                                (do
                                                  if ((__CNTP_CTL_S_ENABLE == 0#1) : Bool)
                                                  then
                                                    (do
                                                      let w__105 ← (( do (__UNKNOWN_bits 32) ) :
                                                        SailM (BitVec 32) )
                                                      (R_set t w__105))
                                                  else
                                                    (do
                                                      let w__106 ← (( do readReg CNTP_CVAL_S ) :
                                                        SailM (BitVec 64) )
                                                      let w__107 ← (( do (PhysicalCountInt ()) ) :
                                                        SailM (BitVec 64) )
                                                      (R_set t
                                                        (Sail.BitVec.extractLsb (w__106 - w__107) 31
                                                          0)))))
                                          else
                                            (do
                                              if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                                              then
                                                (do
                                                  let w__108 ← (( do (__UNKNOWN_bits 32) ) : SailM
                                                    (BitVec 32) )
                                                  (R_set t w__108))
                                              else
                                                (do
                                                  let w__109 ← (( do (CNTP_CVAL_read ()) ) : SailM
                                                    (BitVec 64) )
                                                  let w__110 ← (( do (PhysicalCountInt ()) ) :
                                                    SailM (BitVec 64) )
                                                  (R_set t
                                                    (Sail.BitVec.extractLsb (w__109 - w__110) 31 0))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__115 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__112 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__112) : Bool))))
                        else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__115 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__120 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__117 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__117) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__120 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__124 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__124 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__131 ← (( do
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
                                        let w__128 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                        (pure (((! w__128) : Bool))))
                                    else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__131 : Bool)
                      then
                        (do
                          if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__132 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                              (R_set t w__132))
                          else
                            (do
                              let w__133 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                              let w__134 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__135 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                              (R_set t (Sail.BitVec.extractLsb (w__133 - (w__134 - w__135)) 31 0))))
                      else
                        (do
                          let w__137 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__137 : Bool)
                          then
                            (do
                              if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__138 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                                  (R_set t w__138))
                              else
                                (do
                                  let w__139 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64)
                                    )
                                  let w__140 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  (R_set t (Sail.BitVec.extractLsb (w__139 - w__140) 31 0))))
                          else
                            (do
                              if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__141 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                                  (R_set t w__141))
                              else
                                (do
                                  let w__142 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                                  let w__143 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  (R_set t (Sail.BitVec.extractLsb (w__142 - w__143) 31 0)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__145 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__145 : Bool)
              then
                (do
                  if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__146 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                      (R_set t w__146))
                  else
                    (do
                      let w__147 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                      let w__148 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (w__147 - w__148) 31 0))))
              else
                (do
                  if ((__CNTP_CTL_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__149 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                      (R_set t w__149))
                  else
                    (do
                      let w__150 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                      let w__151 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (w__150 - w__151) 31 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      if ((__CNTP_CTL_S_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__152 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                          (R_set t w__152))
                      else
                        (do
                          let w__153 ← (( do readReg CNTP_CVAL_S ) : SailM (BitVec 64) )
                          let w__154 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__153 - w__154) 31 0))))
                  else
                    (do
                      if ((__CNTP_CTL_NS_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__155 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                          (R_set t w__155))
                      else
                        (do
                          let w__156 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                          let w__157 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__156 - w__157) 31 0)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_SysRegRead32_a44e5d4ed8fbfe64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0VTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0VTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__6)
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
              else (pure false)) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
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
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0VTEN == 0#1) : Bool))) ) : SailM Bool )
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
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
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
                      else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
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
                          else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__51 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__43 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                           (pure (((! w__43) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__45) +++ (_get_HCR_EL2_Type_TGE
                                              w__46)) == 0b11#2) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__48 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_SCR_EL3_Type_NS w__48) == 0#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_SEL2))
                        else (pure false) ) : SailM Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          let w__52 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (__get_CNTHVS_CTL_EL2 w__52) 31 0)))
                      else
                        (do
                          let w__60 ← (( do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__54 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__54) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     let w__56 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__57 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__56) +++ (_get_HCR_EL2_Type_TGE
                                             w__57)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__59 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__59) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              let w__61 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
                              (R_set t (Sail.BitVec.extractLsb (__get_CNTHV_CTL_EL2 w__61) 31 0)))
                          else
                            (do
                              let w__62 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
                              (R_set t (__get_CNTV_CTL w__62)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__66 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__64 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__64) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__66 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__67 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CNTV_CTL w__67))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__68 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CNTV_CTL w__68)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_CNTV_CTL w__69)))
              else (pure (())))))


end ArmFull.Functions
