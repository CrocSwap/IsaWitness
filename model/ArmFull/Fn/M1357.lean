import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0036
import ArmFull.Fn.M0092
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0181
import ArmFull.Fn.M0254
import ArmFull.Fn.M1278

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
def CNTHP_CVAL_EL2_SysRegRead_ed1c928371f03392 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__4)
  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__10 ← (( do
        (pure ((← do
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__9) : Bool)))) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__10 : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__14) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) == 0b10#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE
                                      w__24)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                              w__29)) == 0b11#2) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__31 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_SCR_EL3_Type_NS w__31) == 0#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_SEL2))
                        else (pure false) ) : SailM Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          let w__35 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 w__35))
                      else
                        (do
                          let w__41 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__37) +++ (_get_HCR_EL2_Type_TGE
                                             w__38)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__40 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__40) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__41 : Bool)
                          then
                            (do
                              let w__42 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                              (X_set t 64 w__42))
                          else
                            (do
                              let w__43 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64 w__43))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__47 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__45) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__47 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__51 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__49) == 1#1) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__51 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__56 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__55 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_NV2 w__53) +++ ((_get_HCR_EL2_Type_NV1 w__54) +++ (_get_HCR_EL2_Type_NV
                                  w__55))) == 0b111#3) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__56 : Bool)
                  then
                    (do
                      let w__57 ← (( do (NVMem_read (BitVec.toNat 0x178#12)) ) : SailM (BitVec 64)
                        )
                      (X_set t 64 w__57))
                  else
                    (do
                      let w__58 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 w__58)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__63 ← (( do
                if ((← do
                     if ((← do
                          let w__59 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__59) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__60 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__60) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__63 : Bool)
              then
                (do
                  let w__64 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__64))
              else
                (do
                  let w__67 ← (( do
                    if ((← do
                         let w__65 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__65) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__66 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__66) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__67 : Bool)
                  then
                    (do
                      let w__68 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__68))
                  else
                    (do
                      let w__69 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 w__69))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__70 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 w__70))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegRead_1d2ef372c8b0dab1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__9 ← (( do
        (pure ((← do
              let w__8 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__8) : Bool)))) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__9 : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE
                                          w__24)) == 0b11#2) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_NS w__26) == 0#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        (IsFeatureImplemented FEAT_SEL2))
                    else (pure false) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      let w__30 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHVS_CTL_EL2 w__30)))
                  else
                    (do
                      let w__36 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE
                                         w__33)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__35 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_SCR_EL3_Type_NS w__35) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_CNTHV_CTL_EL2 w__37)))
                      else
                        (do
                          let w__38 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_CNTV_CTL_EL0 w__38))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__40 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__45 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__42) +++ ((_get_HCR_EL2_Type_NV1 w__43) +++ (_get_HCR_EL2_Type_NV
                              w__44))) == 0b111#3) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__45 : Bool)
              then
                (do
                  let w__46 ← (( do (NVMem_read (BitVec.toNat 0x170#12)) ) : SailM (BitVec 64) )
                  (X_set t 64 w__46))
              else
                (do
                  let w__47 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTV_CTL_EL0 w__47)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__52 ← (( do
                if ((← do
                     if ((← do
                          let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__48) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__49 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__49) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__52 : Bool)
              then
                (do
                  let w__53 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHVS_CTL_EL2 w__53)))
              else
                (do
                  let w__56 ← (( do
                    if ((← do
                         let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__54) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__55 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__55) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__56 : Bool)
                  then
                    (do
                      let w__57 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHV_CTL_EL2 w__57)))
                  else
                    (do
                      let w__58 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTV_CTL_EL0 w__58)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__59 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTV_CTL_EL0 w__59)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegRead_aa1abdb084701418 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__9 ← (( do
        (pure ((← do
              let w__8 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__8) : Bool)))) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__9 : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE
                                          w__24)) == 0b11#2) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_NS w__26) == 0#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        (IsFeatureImplemented FEAT_SEL2))
                    else (pure false) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      let w__30 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__30))
                  else
                    (do
                      let w__36 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE
                                         w__33)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__35 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_SCR_EL3_Type_NS w__35) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 w__37))
                      else
                        (do
                          let w__38 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 w__38)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__40 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__45 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__42) +++ ((_get_HCR_EL2_Type_NV1 w__43) +++ (_get_HCR_EL2_Type_NV
                              w__44))) == 0b111#3) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__45 : Bool)
              then
                (do
                  let w__46 ← (( do (NVMem_read (BitVec.toNat 0x168#12)) ) : SailM (BitVec 64) )
                  (X_set t 64 w__46))
              else
                (do
                  let w__47 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 w__47))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__52 ← (( do
                if ((← do
                     if ((← do
                          let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__48) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__49 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__49) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__52 : Bool)
              then
                (do
                  let w__53 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__53))
              else
                (do
                  let w__56 ← (( do
                    if ((← do
                         let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__54) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__55 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__55) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__56 : Bool)
                  then
                    (do
                      let w__57 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__57))
                  else
                    (do
                      let w__58 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 w__58))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__59 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 w__59))
              else (pure (())))))


end ArmFull.Functions
