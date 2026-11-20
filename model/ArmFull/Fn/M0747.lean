module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0066
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0202
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

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_eefece484f7466c9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR14_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 w__10)
  let w__11 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__11)
  let w__12 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  let __AMCR_CG1RZ : (BitVec 1) := (_get_AMCR_Type_CG1RZ w__12)
  let w__13 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__13) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__14.EL == EL0) : Bool)
      then
        (do
          let w__24 ← (( do
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
                                let w__18 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__18) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__22 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__22) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__24 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      let w__25 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__25) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__28) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__30 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__34 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__34) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__40 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__40 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__42) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__48 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                if ((← do
                                                     if ((← do
                                                          (EL2Enabled ())) : Bool)
                                                     then
                                                       (do
                                                         let w__50 ← (( do (ELUsingAArch32 EL1) )
                                                           : SailM Bool )
                                                         (pure (((! w__50) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    let w__52 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    let w__53 ← (( do readReg HCR_EL2 ) : SailM
                                                      (BitVec 64) )
                                                    (pure (((((_get_HCR_EL2_Type_E2H w__52) +++ (_get_HCR_EL2_Type_TGE
                                                            w__53)) != 0b11#2) : Bool))))
                                                else (pure false)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_FGT))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (pure ((← do
                                                let w__57 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                (pure (((! w__57) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                      else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__60 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__64 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__62 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__62) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__64 : Bool)
                                  then
                                    (do
                                      let w__67 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__66 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__67 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                                  else
                                    (do
                                      let w__69 ← (( do
                                        (pure ((← do
                                              (HaveAArch64 ())) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__69 : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) :=
                                            ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          let w__71 ← (( do
                                            (pure ((← do
                                                  let w__70 ← (( do (HaveAArch64 ()) ) : SailM
                                                    Bool )
                                                  (pure (((! w__70) : Bool)))) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__71 : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) :=
                                                ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let w__72 ← (( do (AMEVCNTR1_read 4) ) : SailM
                                                (BitVec 64) )
                                              let w__73 ← (( do (AMEVCNTR1_read 4) ) : SailM
                                                (BitVec 64) )
                                              let (__tup_0, __tup_1) :=
                                                ((Sail.BitVec.extractLsb w__72 63 32), (Sail.BitVec.extractLsb
                                                  w__73 31 0))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          let w__74 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__74.EL == EL1) : Bool)
          then
            (do
              let w__84 ← (( do
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
                                    let w__78 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__82) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__84 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__88 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__86 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__86) : Bool))))
                          else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__92 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__96 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__94 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__94) : Bool))))
                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__96 : Bool)
                          then
                            (do
                              let w__99 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__98 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__98) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__99 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                          else
                            (do
                              let w__104 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__100 ← (( do readReg PSTATE ) : SailM ProcState )
                                           let w__101 ← (( do (IsHighestEL w__100.EL) ) : SailM
                                             Bool )
                                           (pure (((! w__101) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaveAArch64 ()))
                                      else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__104 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__109 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               let w__105 ← (( do readReg PSTATE ) : SailM
                                                 ProcState )
                                               let w__106 ← (( do (IsHighestEL w__105.EL) ) :
                                                 SailM Bool )
                                               (pure (((! w__106) : Bool)))) : Bool)
                                          then
                                            (do
                                              let w__107 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                              (pure (((! w__107) : Bool))))
                                          else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__109 : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) :=
                                        ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let w__110 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64)
                                        )
                                      let w__111 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64)
                                        )
                                      let (__tup_0, __tup_1) :=
                                        ((Sail.BitVec.extractLsb w__110 63 32), (Sail.BitVec.extractLsb
                                          w__111 31 0))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              let w__112 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__112.EL == EL2) : Bool)
              then
                (do
                  let w__122 ← (( do
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
                                        let w__116 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__116) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__120 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__120) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__122 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__126 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__124 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__124) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__126 : Bool)
                      then
                        (do
                          let w__129 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__128 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__128) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__129 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                      else
                        (do
                          let w__134 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__130 ← (( do readReg PSTATE ) : SailM ProcState )
                                       let w__131 ← (( do (IsHighestEL w__130.EL) ) : SailM Bool )
                                       (pure (((! w__131) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaveAArch64 ()))
                                  else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__134 : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__139 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__135 ← (( do readReg PSTATE ) : SailM ProcState )
                                           let w__136 ← (( do (IsHighestEL w__135.EL) ) : SailM
                                             Bool )
                                           (pure (((! w__136) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__137 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                          (pure (((! w__137) : Bool))))
                                      else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__139 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__140 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64) )
                                  let w__141 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__140 63 32), (Sail.BitVec.extractLsb
                                      w__141 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  let w__142 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__142.EL == EL3) : Bool)
                  then
                    (do
                      let w__143 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64) )
                      let w__144 ← (( do (AMEVCNTR1_read 4) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__143 63 32), (Sail.BitVec.extractLsb w__144 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_fa3226080978524b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR110_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 w__10)
  let w__11 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__11)
  let w__12 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  let __AMCR_CG1RZ : (BitVec 1) := (_get_AMCR_Type_CG1RZ w__12)
  let w__13 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  if ((! w__13) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__14.EL == EL0) : Bool)
      then
        (do
          let w__24 ← (( do
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
                                let w__18 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__18) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__22 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__22) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__24 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      let w__25 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__25) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__28) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__30 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__34 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__34) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__40 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__40 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__48 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool
                                               )
                                             (pure (((! w__42) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__44) +++ (_get_HCR_EL2_Type_TGE
                                                w__45)) != 0b11#2) : Bool))))
                                    else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__48 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            (ELUsingAArch32 EL2))
                                        else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__55 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__55) : Bool))))
                                      else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__61 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__61 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__73 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   if ((← do
                                                        if ((← do
                                                             if ((← do
                                                                  (EL2Enabled ())) : Bool)
                                                             then
                                                               (do
                                                                 let w__63 ← (( do
                                                                   (ELUsingAArch32 EL1) ) : SailM
                                                                   Bool )
                                                                 (pure (((! w__63) : Bool))))
                                                             else (pure false)) : Bool)
                                                        then
                                                          (do
                                                            let w__65 ← (( do readReg HCR_EL2 ) :
                                                              SailM (BitVec 64) )
                                                            let w__66 ← (( do readReg HCR_EL2 ) :
                                                              SailM (BitVec 64) )
                                                            (pure (((((_get_HCR_EL2_Type_E2H w__65) +++ (_get_HCR_EL2_Type_TGE
                                                                    w__66)) != 0b11#2) : Bool))))
                                                        else (pure false)) : Bool)
                                                   then
                                                     (do
                                                       (IsFeatureImplemented FEAT_FGT))
                                                   else (pure false)) : Bool)
                                              then
                                                (do
                                                  (pure ((← do
                                                        let w__70 ← (( do (HaveEL EL3) ) : SailM
                                                          Bool )
                                                        (pure (((! w__70) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR110_EL0 == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__73 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let w__77 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__75 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__75) : Bool))))
                                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__77 : Bool)
                                          then
                                            (do
                                              let w__80 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__79 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__79) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__80 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x04#8))))
                                          else
                                            (do
                                              let w__82 ← (( do
                                                (pure ((← do
                                                      (HaveAArch64 ())) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__82 : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) :=
                                                    ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  let w__84 ← (( do
                                                    (pure ((← do
                                                          let w__83 ← (( do (HaveAArch64 ()) ) :
                                                            SailM Bool )
                                                          (pure (((! w__83) : Bool)))) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__84 : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) :=
                                                        ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let w__85 ← (( do (AMEVCNTR1_read 10) ) :
                                                        SailM (BitVec 64) )
                                                      let w__86 ← (( do (AMEVCNTR1_read 10) ) :
                                                        SailM (BitVec 64) )
                                                      let (__tup_0, __tup_1) :=
                                                        ((Sail.BitVec.extractLsb w__85 63 32), (Sail.BitVec.extractLsb
                                                          w__86 31 0))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          let w__87 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__87.EL == EL1) : Bool)
          then
            (do
              let w__97 ← (( do
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
                                    let w__91 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__91) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__95 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__95) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__97 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__102 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__99 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                    (pure (((! w__99) : Bool))))
                                else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__102 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__115 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__115 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__119 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__117 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__117) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__119 : Bool)
                                  then
                                    (do
                                      let w__122 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__121 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__121) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__122 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                                  else
                                    (do
                                      let w__127 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   let w__123 ← (( do readReg PSTATE ) : SailM
                                                     ProcState )
                                                   let w__124 ← (( do (IsHighestEL w__123.EL) ) :
                                                     SailM Bool )
                                                   (pure (((! w__124) : Bool)))) : Bool)
                                              then
                                                (do
                                                  (HaveAArch64 ()))
                                              else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__127 : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) :=
                                            ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          let w__132 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       let w__128 ← (( do readReg PSTATE ) : SailM
                                                         ProcState )
                                                       let w__129 ← (( do (IsHighestEL w__128.EL)
                                                         ) : SailM Bool )
                                                       (pure (((! w__129) : Bool)))) : Bool)
                                                  then
                                                    (do
                                                      let w__130 ← (( do (HaveAArch64 ()) ) :
                                                        SailM Bool )
                                                      (pure (((! w__130) : Bool))))
                                                  else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__132 : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) :=
                                                ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let w__133 ← (( do (AMEVCNTR1_read 10) ) : SailM
                                                (BitVec 64) )
                                              let w__134 ← (( do (AMEVCNTR1_read 10) ) : SailM
                                                (BitVec 64) )
                                              let (__tup_0, __tup_1) :=
                                                ((Sail.BitVec.extractLsb w__133 63 32), (Sail.BitVec.extractLsb
                                                  w__134 31 0))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              let w__135 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__135.EL == EL2) : Bool)
              then
                (do
                  let w__145 ← (( do
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
                                        let w__139 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__139) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__143 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__143) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__145 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__149 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__147 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__147) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__149 : Bool)
                      then
                        (do
                          let w__152 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__151 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__151) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__152 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                      else
                        (do
                          let w__157 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__153 ← (( do readReg PSTATE ) : SailM ProcState )
                                       let w__154 ← (( do (IsHighestEL w__153.EL) ) : SailM Bool )
                                       (pure (((! w__154) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaveAArch64 ()))
                                  else (pure false)) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__157 : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let w__162 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__158 ← (( do readReg PSTATE ) : SailM ProcState )
                                           let w__159 ← (( do (IsHighestEL w__158.EL) ) : SailM
                                             Bool )
                                           (pure (((! w__159) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__160 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                          (pure (((! w__160) : Bool))))
                                      else (pure false)) && ((__AMCR_CG1RZ == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__162 : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let w__163 ← (( do (AMEVCNTR1_read 10) ) : SailM (BitVec 64) )
                                  let w__164 ← (( do (AMEVCNTR1_read 10) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__163 63 32), (Sail.BitVec.extractLsb
                                      w__164 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  let w__165 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__165.EL == EL3) : Bool)
                  then
                    (do
                      let w__166 ← (( do (AMEVCNTR1_read 10) ) : SailM (BitVec 64) )
                      let w__167 ← (( do (AMEVCNTR1_read 10) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__166 63 32), (Sail.BitVec.extractLsb w__167 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


end ArmFull.Functions
