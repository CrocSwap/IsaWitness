module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0137
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0258 set_option backward.proofsInPublic true @[expose] public section

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
def CNTHVS_CTL_SysRegWrite32_018e2cf152f109f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__52 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_CNTHVS_CTL_EL2
                            (Mk_CNTHVS_CTL_EL2_Type (Sail.BitVec.zeroExtend w__52 64))))
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
                              let w__61 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_CNTHV_CTL_EL2
                                (Mk_CNTHV_CTL_EL2_Type (Sail.BitVec.zeroExtend w__61 64))))
                          else
                            (do
                              let w__62 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_CNTV_CTL (Mk_CNTV_CTL_Type w__62)))))))))
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
              let w__67 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (__set_CNTV_CTL (Mk_CNTV_CTL_Type w__67))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__68 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (__set_CNTV_CTL (Mk_CNTV_CTL_Type w__68)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_CNTV_CTL (Mk_CNTV_CTL_Type w__69)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTV_TVAL_SysRegWrite32_903e727583f63e89 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__52 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          let w__53 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend w__52 64)) + w__53)))
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
                              let w__62 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              let w__63 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type
                                ((Sail.BitVec.castWidth (m := 64) (sign_extend w__62 64)) + w__63)))
                          else
                            (do
                              let w__66 ← (( do
                                if ((← do
                                     (HaveEL EL2)) : Bool)
                                then
                                  (do
                                    let w__65 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                    (pure (((! w__65) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__66 : Bool)
                              then
                                (do
                                  let w__67 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  let w__68 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  let w__69 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                                  (CNTV_CVAL_write
                                    (Mk_CNTV_CVAL_Type
                                      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                            w__67 64)) + w__68)) - w__69))))
                              else
                                (do
                                  let w__72 ← (( do
                                    if ((← do
                                         (HaveEL EL2)) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false) ) : SailM Bool )
                                  if (w__72 : Bool)
                                  then
                                    (do
                                      let w__73 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      let w__74 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      let w__75 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                                      (CNTV_CVAL_write
                                        (Mk_CNTV_CVAL_Type
                                          ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                                w__73 64)) + w__74)) - w__75))))
                                  else
                                    (do
                                      let w__76 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      let w__77 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      (CNTV_CVAL_write
                                        (Mk_CNTV_CVAL_Type
                                          ((Sail.BitVec.castWidth (m := 64) (sign_extend w__76 64)) + w__77))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__81 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__79 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__79) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__81 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__84 ← (( do
                if ((← do
                     (HaveEL EL2)) : Bool)
                then
                  (do
                    let w__83 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__83) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__84 : Bool)
              then
                (do
                  let w__85 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  let w__86 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__87 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  (CNTV_CVAL_write
                    (Mk_CNTV_CVAL_Type
                      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            w__85 64)) + w__86)) - w__87))))
              else
                (do
                  let w__90 ← (( do
                    if ((← do
                         (HaveEL EL2)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false) ) : SailM Bool )
                  if (w__90 : Bool)
                  then
                    (do
                      let w__91 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__92 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__93 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      (CNTV_CVAL_write
                        (Mk_CNTV_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                w__91 64)) + w__92)) - w__93))))
                  else
                    (do
                      let w__94 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__95 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (CNTV_CVAL_write
                        (Mk_CNTV_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) (sign_extend w__94 64)) + w__95)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__96 ← (( do (R_read t) ) : SailM (BitVec 32) )
              let w__97 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              let w__98 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
              (CNTV_CVAL_write
                (Mk_CNTV_CVAL_Type
                  ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        w__96 64)) + w__97)) - w__98))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__99 ← (( do (HaveEL EL2) ) : SailM Bool )
                  if (w__99 : Bool)
                  then
                    (do
                      let w__100 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__101 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__102 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      (CNTV_CVAL_write
                        (Mk_CNTV_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                w__100 64)) + w__101)) - w__102))))
                  else
                    (do
                      let w__103 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__104 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (CNTV_CVAL_write
                        (Mk_CNTV_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) (sign_extend w__103 64)) + w__104)))))
              else (pure (())))))


end ArmFull.Functions
