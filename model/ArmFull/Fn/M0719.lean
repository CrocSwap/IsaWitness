import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0066
import ArmFull.Fn.M0080
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
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
def AMEVCNTR1_SysRegRead64_6f64074808614759 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__0)
  let w__1 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (AMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __AMUSERENR_EN : (BitVec 1) := (_get_AMUSERENR_Type_EN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__5)
  let w__6 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__6)
  let w__7 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__7)
  let w__8 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__8)
  let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__9)
  let w__10 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR16_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 w__10)
  let w__11 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__11)
  let w__12 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  let __AMCR_CG1RZ : (BitVec 1) := (_get_AMCR_Type_CG1RZ w__12)
  let w__13 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__13) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__14.EL == EL0) : Bool)
      then
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__17 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__17) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__21 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__21) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      let w__24 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__24) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__27) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__31 : Bool)
                  then
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__33) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__35 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__39 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__39 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__41 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__41) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__47 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__47 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      (pure ((← do
                                            if ((← do
                                                 if ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          let w__49 ← (( do (ELUsingAArch32 EL1) )
                                                            : SailM Bool )
                                                          (pure (((! w__49) : Bool))))
                                                      else (pure false)) : Bool)
                                                 then
                                                   (do
                                                     let w__51 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     let w__52 ← (( do readReg HCR_EL2 ) : SailM
                                                       (BitVec 64) )
                                                     (pure (((((_get_HCR_EL2_Type_E2H w__51) +++ (_get_HCR_EL2_Type_TGE
                                                             w__52)) != 0b11#2) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                (IsFeatureImplemented FEAT_FGT))
                                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR16_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__60 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              let w__58 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__58) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__60 : Bool)
                                  then
                                    (do
                                      let w__63 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__62 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__62) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__63 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                                  else
                                    (do
                                      let w__65 ← (( do
                                        (pure ((← do
                                              (HaveAArch64 ())) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__65 : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) :=
                                            ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          let w__67 ← (( do
                                            (pure ((← do
                                                  let w__66 ← (( do (HaveAArch64 ()) ) : SailM
                                                    Bool )
                                                  (pure (((! w__66) : Bool)))) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__67 : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) :=
                                                ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let w__68 ← (( do (AMEVCNTR1_read 6) ) : SailM
                                                (BitVec 64) )
                                              let w__69 ← (( do (AMEVCNTR1_read 6) ) : SailM
                                                (BitVec 64) )
                                              let (__tup_0, __tup_1) :=
                                                ((Sail.BitVec.extractLsb w__68 63 32), (Sail.BitVec.extractLsb
                                                  w__69 31 0))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          let w__70 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__70.EL == EL1) : Bool)
          then
            (do
              let w__79 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__73 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__77 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__77) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__79 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__83 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__81 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__81) : Bool))))
                          else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__83 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__87 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__87 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__90 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__88 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__88) : Bool))))
                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__90 : Bool)
                          then
                            (do
                              let w__93 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__92 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__93 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                          else
                            (do
                              let w__97 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__94 ← (( do readReg PSTATE ) : SailM ProcState )
                                           (pure (((! (IsHighestEL w__94.EL)) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaveAArch64 ()))
                                      else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__97 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__101 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               let w__98 ← (( do readReg PSTATE ) : SailM
                                                 ProcState )
                                               (pure (((! (IsHighestEL w__98.EL)) : Bool)))) : Bool)
                                          then
                                            (do
                                              let w__99 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                              (pure (((! w__99) : Bool))))
                                          else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__101 : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) :=
                                        ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let w__102 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64)
                                        )
                                      let w__103 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64)
                                        )
                                      let (__tup_0, __tup_1) :=
                                        ((Sail.BitVec.extractLsb w__102 63 32), (Sail.BitVec.extractLsb
                                          w__103 31 0))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              let w__104 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__104.EL == EL2) : Bool)
              then
                (do
                  let w__113 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__107 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__107) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__111 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__111) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__113 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__116 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__114 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__114) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__116 : Bool)
                      then
                        (do
                          let w__119 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__118 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__118) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__119 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                      else
                        (do
                          let w__123 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__120 ← (( do readReg PSTATE ) : SailM ProcState )
                                       (pure (((! (IsHighestEL w__120.EL)) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaveAArch64 ()))
                                  else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__123 : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__127 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__124 ← (( do readReg PSTATE ) : SailM ProcState )
                                           (pure (((! (IsHighestEL w__124.EL)) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__125 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                          (pure (((! w__125) : Bool))))
                                      else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__127 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__128 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64) )
                                  let w__129 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__128 63 32), (Sail.BitVec.extractLsb
                                      w__129 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  let w__130 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__130.EL == EL3) : Bool)
                  then
                    (do
                      let w__131 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64) )
                      let w__132 ← (( do (AMEVCNTR1_read 6) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__131 63 32), (Sail.BitVec.extractLsb w__132 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_839ed88b8f796549 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__0)
  let w__1 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (AMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __AMUSERENR_EN : (BitVec 1) := (_get_AMUSERENR_Type_EN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__5)
  let w__6 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__6)
  let w__7 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__7)
  let w__8 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__8)
  let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__9)
  let w__10 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR111_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 w__10)
  let w__11 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__11)
  let w__12 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  let __AMCR_CG1RZ : (BitVec 1) := (_get_AMCR_Type_CG1RZ w__12)
  let w__13 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__13) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__14.EL == EL0) : Bool)
      then
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__17 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__17) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__21 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__21) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      let w__24 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__24) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__27) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__31 : Bool)
                  then
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__33) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__35 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__39 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__39 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__47 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__41 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool
                                               )
                                             (pure (((! w__41) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__43) +++ (_get_HCR_EL2_Type_TGE
                                                w__44)) != 0b11#2) : Bool))))
                                    else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__47 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            (ELUsingAArch32 EL2))
                                        else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__56 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__54 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__54) : Bool))))
                                      else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__56 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__60 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__60 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__70 ← (( do
                                        (pure ((← do
                                              (pure ((← do
                                                    if ((← do
                                                         if ((← do
                                                              if ((← do
                                                                   (EL2Enabled ())) : Bool)
                                                              then
                                                                (do
                                                                  let w__62 ← (( do
                                                                    (ELUsingAArch32 EL1) ) : SailM
                                                                    Bool )
                                                                  (pure (((! w__62) : Bool))))
                                                              else (pure false)) : Bool)
                                                         then
                                                           (do
                                                             let w__64 ← (( do readReg HCR_EL2 ) :
                                                               SailM (BitVec 64) )
                                                             let w__65 ← (( do readReg HCR_EL2 ) :
                                                               SailM (BitVec 64) )
                                                             (pure (((((_get_HCR_EL2_Type_E2H w__64) +++ (_get_HCR_EL2_Type_TGE
                                                                     w__65)) != 0b11#2) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        (IsFeatureImplemented FEAT_FGT))
                                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__70 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let w__73 ← (( do
                                            (pure ((← do
                                                  if (((HaveEL EL3) : Bool) : Bool)
                                                  then
                                                    (do
                                                      let w__71 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__71) : Bool))))
                                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__73 : Bool)
                                          then
                                            (do
                                              let w__76 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__75 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__76 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x04#8))))
                                          else
                                            (do
                                              let w__78 ← (( do
                                                (pure ((← do
                                                      (HaveAArch64 ())) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__78 : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) :=
                                                    ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  let w__80 ← (( do
                                                    (pure ((← do
                                                          let w__79 ← (( do (HaveAArch64 ()) ) :
                                                            SailM Bool )
                                                          (pure (((! w__79) : Bool)))) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__80 : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) :=
                                                        ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let w__81 ← (( do (AMEVCNTR1_read 11) ) :
                                                        SailM (BitVec 64) )
                                                      let w__82 ← (( do (AMEVCNTR1_read 11) ) :
                                                        SailM (BitVec 64) )
                                                      let (__tup_0, __tup_1) :=
                                                        ((Sail.BitVec.extractLsb w__81 63 32), (Sail.BitVec.extractLsb
                                                          w__82 31 0))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          let w__83 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__83.EL == EL1) : Bool)
          then
            (do
              let w__92 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__86 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__90) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__92 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__97 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__94 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                    (pure (((! w__94) : Bool))))
                                else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__97 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__102 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__102 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__106 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__104 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__104) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__106 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__110 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__110 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__113 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              let w__111 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__111) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__113 : Bool)
                                  then
                                    (do
                                      let w__116 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__115 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__115) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__116 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                                  else
                                    (do
                                      let w__120 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   let w__117 ← (( do readReg PSTATE ) : SailM
                                                     ProcState )
                                                   (pure (((! (IsHighestEL w__117.EL)) : Bool)))) : Bool)
                                              then
                                                (do
                                                  (HaveAArch64 ()))
                                              else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__120 : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) :=
                                            ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          let w__124 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       let w__121 ← (( do readReg PSTATE ) : SailM
                                                         ProcState )
                                                       (pure (((! (IsHighestEL w__121.EL)) : Bool)))) : Bool)
                                                  then
                                                    (do
                                                      let w__122 ← (( do (HaveAArch64 ()) ) :
                                                        SailM Bool )
                                                      (pure (((! w__122) : Bool))))
                                                  else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__124 : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) :=
                                                ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let w__125 ← (( do (AMEVCNTR1_read 11) ) : SailM
                                                (BitVec 64) )
                                              let w__126 ← (( do (AMEVCNTR1_read 11) ) : SailM
                                                (BitVec 64) )
                                              let (__tup_0, __tup_1) :=
                                                ((Sail.BitVec.extractLsb w__125 63 32), (Sail.BitVec.extractLsb
                                                  w__126 31 0))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              let w__127 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__127.EL == EL2) : Bool)
              then
                (do
                  let w__136 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__130 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__130) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__134 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__134) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__136 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__139 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__137 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__137) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__139 : Bool)
                      then
                        (do
                          let w__142 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__141 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__141) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__142 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                      else
                        (do
                          let w__146 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__143 ← (( do readReg PSTATE ) : SailM ProcState )
                                       (pure (((! (IsHighestEL w__143.EL)) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaveAArch64 ()))
                                  else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__146 : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__150 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__147 ← (( do readReg PSTATE ) : SailM ProcState )
                                           (pure (((! (IsHighestEL w__147.EL)) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__148 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                          (pure (((! w__148) : Bool))))
                                      else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__150 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__151 ← (( do (AMEVCNTR1_read 11) ) : SailM (BitVec 64) )
                                  let w__152 ← (( do (AMEVCNTR1_read 11) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__151 63 32), (Sail.BitVec.extractLsb
                                      w__152 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  let w__153 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__153.EL == EL3) : Bool)
                  then
                    (do
                      let w__154 ← (( do (AMEVCNTR1_read 11) ) : SailM (BitVec 64) )
                      let w__155 ← (( do (AMEVCNTR1_read 11) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__154 63 32), (Sail.BitVec.extractLsb w__155 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


end ArmFull.Functions
