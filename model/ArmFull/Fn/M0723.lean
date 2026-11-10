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
import ArmFull.Fn.M0079
import ArmFull.Fn.M0081
import ArmFull.Fn.M0092
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

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHPS_CVAL_SysRegRead64_aa5fa6170d1a3db5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let w__10 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
        (pure ((← do
              if ((← do
                   let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then
                (do
                  let w__15 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__33) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__38) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                      w__41)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
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
                                          w__48)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__64 ← (( do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               if ((← do
                                                    (EL2Enabled ())) : Bool)
                                               then
                                                 (do
                                                   let w__56 ← (( do (ELUsingAArch32 EL2) ) :
                                                     SailM Bool )
                                                   (pure (((! w__56) : Bool))))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              let w__58 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              let w__59 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              (pure (((((_get_HCR_EL2_Type_E2H w__58) +++ (_get_HCR_EL2_Type_TGE
                                                      w__59)) == 0b11#2) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__61 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                         (pure ((((_get_SCR_EL3_Type_NS w__61) == 0#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_SEL2))
                                else (pure false) ) : SailM Bool )
                              if (w__64 : Bool)
                              then
                                (do
                                  let w__65 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64)
                                    )
                                  let w__66 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64)
                                    )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__65 63 32), (Sail.BitVec.extractLsb
                                      w__66 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__74 ← (( do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__68) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__70 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__71 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__70) +++ (_get_HCR_EL2_Type_TGE
                                                     w__71)) == 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__73 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure ((((_get_SCR_EL3_Type_NS w__73) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__74 : Bool)
                                  then
                                    (do
                                      let w__75 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM
                                        (BitVec 64) )
                                      let w__76 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM
                                        (BitVec 64) )
                                      let (__tup_0, __tup_1) :=
                                        ((Sail.BitVec.extractLsb w__75 63 32), (Sail.BitVec.extractLsb
                                          w__76 31 0))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let w__77 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64)
                                        )
                                      let w__78 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64)
                                        )
                                      let (__tup_0, __tup_1) :=
                                        ((Sail.BitVec.extractLsb w__77 63 32), (Sail.BitVec.extractLsb
                                          w__78 31 0))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__83 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__80 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__80) : Bool))))
                        else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__83 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__88 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__85 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__85) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__88 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__92 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__92 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__94 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL3))
                        else (pure false) ) : SailM Bool )
                      if (w__94 : Bool)
                      then
                        (do
                          let w__95 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                          let w__96 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__95 63 32), (Sail.BitVec.extractLsb w__96 31
                              0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          let w__97 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__98 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__97 63 32), (Sail.BitVec.extractLsb w__98 31
                              0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__100 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__100 : Bool)
              then
                (do
                  let w__101 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                  let w__102 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__101 63 32), (Sail.BitVec.extractLsb w__102 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let w__103 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                  let w__104 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__103 63 32), (Sail.BitVec.extractLsb w__104 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__105 ← (( do readReg CNTP_CVAL_S ) : SailM (BitVec 64) )
                      let w__106 ← (( do readReg CNTP_CVAL_S ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__105 63 32), (Sail.BitVec.extractLsb w__106 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__107 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                      let w__108 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__107 63 32), (Sail.BitVec.extractLsb w__108 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHV_CVAL_SysRegRead64_7bf312f271feb72e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
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
                      else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool
                )
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
                          else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
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
                          let w__52 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__53 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__52 63 32), (Sail.BitVec.extractLsb w__53 31
                              0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          let w__61 ← (( do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__55 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__55) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     let w__57 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__58 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__57) +++ (_get_HCR_EL2_Type_TGE
                                             w__58)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__60 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__60) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__61 : Bool)
                          then
                            (do
                              let w__62 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                              let w__63 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__62 63 32), (Sail.BitVec.extractLsb w__63
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__64 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                              let w__65 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__64 63 32), (Sail.BitVec.extractLsb w__65
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__69 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__67 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__67) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__69 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__70 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
              let w__71 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) :=
                ((Sail.BitVec.extractLsb w__70 63 32), (Sail.BitVec.extractLsb w__71 31 0))
              (R_set t2 __tup_0)
              (R_set t __tup_1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__72 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
              let w__73 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) :=
                ((Sail.BitVec.extractLsb w__72 63 32), (Sail.BitVec.extractLsb w__73 31 0))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__74 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                  let w__75 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__74 63 32), (Sail.BitVec.extractLsb w__75 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


end ArmFull.Functions
