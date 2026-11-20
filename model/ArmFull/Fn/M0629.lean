module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0212
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
def CNTV_TVAL_SysRegRead32_ac1a47c2d11f8dd9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__7 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHVS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHVS_CTL_EL2_Type_ENABLE w__7)
  let w__8 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHV_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHV_CTL_EL2_Type_ENABLE w__8)
  let w__9 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
  let __CNTV_CTL_ENABLE : (BitVec 1) := (_get_CNTV_CTL_Type_ENABLE w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__16 ← (( do
        (pure ((← do
              if ((← do
                   let w__10 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__10) : Bool)))) : Bool)
              then
                (do
                  let w__14 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__12) +++ (_get_HCR_EL2_Type_TGE w__13)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__14) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__16 : Bool)
      then
        (do
          let w__20 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__18 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__18) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__20 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__22 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__24) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__30 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__37 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                               (pure (((! w__32) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__34) +++ (_get_HCR_EL2_Type_TGE w__35)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__37 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__39) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__41) +++ (_get_HCR_EL2_Type_TGE
                                      w__42)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__54 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__46 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                           (pure (((! w__46) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__48) +++ (_get_HCR_EL2_Type_TGE
                                              w__49)) == 0b11#2) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__51 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_SCR_EL3_Type_NS w__51) == 0#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_SEL2))
                        else (pure false) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__55 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                              (R_set t w__55))
                          else
                            (do
                              let w__56 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                              let w__57 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (R_set t (Sail.BitVec.extractLsb (w__56 - w__57) 31 0))))
                      else
                        (do
                          let w__65 ← (( do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__59 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__59) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     let w__61 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__62 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__61) +++ (_get_HCR_EL2_Type_TGE
                                             w__62)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__64 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__64) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__65 : Bool)
                          then
                            (do
                              if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__66 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                                  (R_set t w__66))
                              else
                                (do
                                  let w__67 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                                  let w__68 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  (R_set t (Sail.BitVec.extractLsb (w__67 - w__68) 31 0))))
                          else
                            (do
                              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__69 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                                  (R_set t w__69))
                              else
                                (do
                                  let w__72 ← (( do
                                    if ((← do
                                         (HaveEL EL2)) : Bool)
                                    then
                                      (do
                                        let w__71 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                        (pure (((! w__71) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__72 : Bool)
                                  then
                                    (do
                                      let w__73 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64)
                                        )
                                      let w__74 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      let w__75 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64)
                                        )
                                      (R_set t
                                        (Sail.BitVec.extractLsb (w__73 - (w__74 - w__75)) 31 0)))
                                  else
                                    (do
                                      let w__78 ← (( do
                                        if ((← do
                                             (HaveEL EL2)) : Bool)
                                        then
                                          (do
                                            (ELUsingAArch32 EL2))
                                        else (pure false) ) : SailM Bool )
                                      if (w__78 : Bool)
                                      then
                                        (do
                                          let w__79 ← (( do (CNTV_CVAL_read ()) ) : SailM
                                            (BitVec 64) )
                                          let w__80 ← (( do (PhysicalCountInt ()) ) : SailM
                                            (BitVec 64) )
                                          let w__81 ← (( do (CNTVOFF_read ()) ) : SailM
                                            (BitVec 64) )
                                          (R_set t
                                            (Sail.BitVec.extractLsb (w__79 - (w__80 - w__81)) 31 0)))
                                      else
                                        (do
                                          let w__82 ← (( do (CNTV_CVAL_read ()) ) : SailM
                                            (BitVec 64) )
                                          let w__83 ← (( do (PhysicalCountInt ()) ) : SailM
                                            (BitVec 64) )
                                          (R_set t (Sail.BitVec.extractLsb (w__82 - w__83) 31 0))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__87 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__85 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__85) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__87 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
              then
                (do
                  let w__88 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                  (R_set t w__88))
              else
                (do
                  let w__91 ← (( do
                    if ((← do
                         (HaveEL EL2)) : Bool)
                    then
                      (do
                        let w__90 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__90) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__91 : Bool)
                  then
                    (do
                      let w__92 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                      let w__93 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__94 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (w__92 - (w__93 - w__94)) 31 0)))
                  else
                    (do
                      let w__97 ← (( do
                        if ((← do
                             (HaveEL EL2)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false) ) : SailM Bool )
                      if (w__97 : Bool)
                      then
                        (do
                          let w__98 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__99 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__100 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__98 - (w__99 - w__100)) 31 0)))
                      else
                        (do
                          let w__101 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__102 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__101 - w__102) 31 0)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
              then
                (do
                  let w__103 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                  (R_set t w__103))
              else
                (do
                  let w__104 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                  let w__105 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__106 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                  (R_set t (Sail.BitVec.extractLsb (w__104 - (w__105 - w__106)) 31 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTV_CTL_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__107 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                      (R_set t w__107))
                  else
                    (do
                      let w__108 ← (( do (HaveEL EL2) ) : SailM Bool )
                      if (w__108 : Bool)
                      then
                        (do
                          let w__109 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__110 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__111 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__109 - (w__110 - w__111)) 31 0)))
                      else
                        (do
                          let w__112 ← (( do (CNTV_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__113 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__112 - w__113) 31 0)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CONTEXTIDR_SysRegRead32_a8d33c511e223d46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TRVM : (BitVec 1) := (_get_HCR_Type_TRVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TRVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__24 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__25 ← (( do (CONTEXTIDR_NS_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__25))
                          else
                            (do
                              let w__26 ← (( do (CONTEXTIDR_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__26)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__30 ← (( do (CONTEXTIDR_NS_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__30))
              else
                (do
                  let w__31 ← (( do (CONTEXTIDR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__31)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__32 ← (( do readReg CONTEXTIDR_S ) : SailM (BitVec 32) )
                      (R_set t w__32))
                  else
                    (do
                      let w__33 ← (( do (CONTEXTIDR_NS_read ()) ) : SailM (BitVec 32) )
                      (R_set t w__33)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPACR_SysRegRead32_3e95a711394f5115 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TCPAC : (BitVec 1) := (_get_CPTR_EL3_Type_TCPAC w__1)
  let w__2 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__2)
  let w__3 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__3)
  let w__4 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TCPAC : (BitVec 1) := (_get_CPTR_EL2_Type_TCPAC w__4)
  let w__5 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TCPAC : (BitVec 1) := (_get_HCPTR_Type_TCPAC w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__15 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__9) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__13 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__13) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__17 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__17) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__23 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__25) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TCPAC == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TCPAC == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__31 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__33 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__33) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__35 : Bool)
                              then
                                (do
                                  let w__38 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__37 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__37) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__38 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__39 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
                                  let w__40 ← (( do (__get_CPACR w__39) ) : SailM (BitVec 32) )
                                  (R_set t w__40))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__50 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__44 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__44) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__48 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__48) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__50 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__54 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__52 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__52) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__54 : Bool)
                  then
                    (do
                      let w__57 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__56 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__56) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__57 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__58 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
                      let w__59 ← (( do (__get_CPACR w__58) ) : SailM (BitVec 32) )
                      (R_set t w__59))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__60 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
                  let w__61 ← (( do (__get_CPACR w__60) ) : SailM (BitVec 32) )
                  (R_set t w__61))
              else (pure (())))))


end ArmFull.Functions
