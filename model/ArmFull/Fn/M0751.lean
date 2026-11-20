module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
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
def HTTBR_SysRegRead64_5b679aebf4474d8a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T2 : (BitVec 1) := (_get_HSTR_EL2_Type_T2 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T2 : (BitVec 1) := (_get_HSTR_Type_T2 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T2 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
              let w__13 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) :=
                ((Sail.BitVec.extractLsb w__12 63 32), (Sail.BitVec.extractLsb w__13 31 0))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__14 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
                      let w__15 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__14 63 32), (Sail.BitVec.extractLsb w__15 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_SysRegRead64_bd143a1fe560ae4b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__14 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__15 63 32), (Sail.BitVec.extractLsb w__16 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__17 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                      let w__18 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__17 63 32), (Sail.BitVec.extractLsb w__18 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__21 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  let w__22 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                  let w__23 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__22 63 32), (Sail.BitVec.extractLsb w__23 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let w__24 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                  let w__25 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__24 63 32), (Sail.BitVec.extractLsb w__25 31 0))
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
                      let w__26 ← (( do readReg PAR_S ) : SailM (BitVec 64) )
                      let w__27 ← (( do readReg PAR_S ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__26 63 32), (Sail.BitVec.extractLsb w__27 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let w__28 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__29 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__28 63 32), (Sail.BitVec.extractLsb w__29 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PMCCNTR_SysRegRead64_1cf48d19bc879bd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T9 : (BitVec 1) := (_get_HSTR_EL2_Type_T9 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T9 : (BitVec 1) := (_get_HSTR_Type_T9 w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMCCNTR_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMCCNTR_EL0 w__7)
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
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
                            let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__31 ← (( do
            if ((← do
                 let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__20) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__23 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__24 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__22) +++ ((_get_PMUSERENR_EL0_Type_CR
                                   w__23) +++ (_get_PMUSERENR_EL0_Type_EN w__24))) == 0b000#3) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         let w__26 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                         (pure (((! w__26) : Bool)))) : Bool)
                    then
                      (do
                        let w__27 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        let w__28 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                        (pure (((((_get_PMUSERENR_EL0_Type_CR w__27) +++ (_get_PMUSERENR_EL0_Type_EN
                                w__28)) == 0b00#2) : Bool))))
                    else (pure false)))
            else (pure false) ) : SailM Bool )
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
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__35 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__39 ← (( do
                if ((← do
                     (ELUsingAArch32 EL1)) : Bool)
                then
                  (do
                    let w__37 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    let w__38 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
                    (pure (((((_get_PMUSERENR_Type_CR w__37) +++ (_get_PMUSERENR_Type_EN w__38)) == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__41 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__41) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__47 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
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
                                      w__52)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__70 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 if ((← do
                                                      (EL2Enabled ())) : Bool)
                                                 then
                                                   (do
                                                     let w__60 ← (( do (ELUsingAArch32 EL1) ) :
                                                       SailM Bool )
                                                     (pure (((! w__60) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                let w__62 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                let w__63 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                (pure (((((_get_HCR_EL2_Type_E2H w__62) +++ (_get_HCR_EL2_Type_TGE
                                                        w__63)) != 0b11#2) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_FGT))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (pure ((← do
                                            let w__67 ← (( do (HaveEL EL3) ) : SailM Bool )
                                            (pure (((! w__67) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                  else (pure false)) && ((__HDFGRTR_EL2_PMCCNTR_EL0 == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__70 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__74 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__72 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__72) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__74 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__78 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__78 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__82 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__80 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__80) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__82 : Bool)
                                      then
                                        (do
                                          let w__85 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__84 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__84) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__85 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__86 ← (( do (PMCCNTR_read ()) ) : SailM
                                            (BitVec 64) )
                                          let w__87 ← (( do (PMCCNTR_read ()) ) : SailM
                                            (BitVec 64) )
                                          let (__tup_0, __tup_1) :=
                                            ((Sail.BitVec.extractLsb w__86 63 32), (Sail.BitVec.extractLsb
                                              w__87 31 0))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__97 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__101 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__99 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__99) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
              if (w__101 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__105 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__105 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__109 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__107 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__107) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__109 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__113 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__113 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__117 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__115 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__115) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__117 : Bool)
                              then
                                (do
                                  let w__120 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__119 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__119) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__120 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__121 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                                  let w__122 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__121 63 32), (Sail.BitVec.extractLsb
                                      w__122 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__132 ← (( do
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
                                    let w__126 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__126) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__130 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__130) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__132 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__136 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__134 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__134) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__136 : Bool)
                  then
                    (do
                      let w__139 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__138 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__138) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__139 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__140 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                      let w__141 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__140 63 32), (Sail.BitVec.extractLsb w__141 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__142 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                  let w__143 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__142 63 32), (Sail.BitVec.extractLsb w__143 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


end ArmFull.Functions
