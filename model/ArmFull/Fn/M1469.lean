import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0058
import ArmFull.Fn.M0071
import ArmFull.Fn.M0073
import ArmFull.Fn.M0080
import ArmFull.Fn.M0087
import ArmFull.Fn.M0113
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0164
import ArmFull.Fn.M0167
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0192
import ArmFull.Fn.M0200
import ArmFull.Fn.M0254
import ArmFull.Fn.M1468

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

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysRegRead (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let index ← (( do (undefined_int_at (← occLabel 2895) ()) ) : SailME Unit Int )
  let n ← (( do (undefined_int_at (← occLabel 2896) ()) ) : SailME Unit Int )
  if ((((op0 == 3) && (op1 == 3)) && (crn == 13)) : Bool)
  then
    (do
      let n : Int :=
        (BitVec.toNat
          ((BitVec.setWidth 1 (BitVec.join1 [(integer_access crm 0)])) +++ (integer_subrange op2 2 0)))
      if ((((Sail.BitVec.castWidth (m := 3) (integer_subrange crm 3 1)) == 0b010#3) || ((Sail.BitVec.castWidth (m := 3) (integer_subrange
               crm 3 1)) == 0b011#3)) : Bool)
      then
        (do
          let w__0 ← (( do readReg AMCGCR_EL0 ) : SailME Unit (BitVec 64) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC w__0))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else
        (do
          if ((((Sail.BitVec.castWidth (m := 3) (integer_subrange crm 3 1)) == 0b110#3) || ((Sail.BitVec.castWidth (m := 3) (integer_subrange
                   crm 3 1)) == 0b111#3)) : Bool)
          then
            (do
              let w__1 ← (( do readReg AMCGCR_EL0 ) : SailME Unit (BitVec 64) )
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC w__1))) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))))
  else (pure (()))
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 14)) && (((Sail.BitVec.castWidth (m := 2) (integer_subrange
               crm 3 2)) == 0b10#2) || ((Sail.BitVec.castWidth (m := 2) (integer_subrange crm 3 2)) == 0b11#2))) && ((Sail.BitVec.castWidth (m := 5) ((integer_subrange
             crm 1 0) +++ (integer_subrange op2 2 0))) != 0b11111#5)) : Bool)
  then
    (do
      let w__17 ← (( do
        if ((← do
             let w__2 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
             (pure ((((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__2 -i 1)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__4 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__4.EL == EL1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         if ((← do
                              let w__5 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__5.EL == EL0) : Bool)))) : Bool)
                         then
                           (do
                             if ((← do
                                  if ((((Sail.BitVec.castWidth (m := 2) (integer_subrange crm 3 2)) == 0b10#2) : Bool) : Bool)
                                  then
                                    (do
                                      let w__6 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                        (BitVec 64) )
                                      let w__7 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                        (BitVec 64) )
                                      (pure (((((_get_PMUSERENR_EL0_Type_ER w__6) +++ (_get_PMUSERENR_EL0_Type_EN
                                              w__7)) != 0b00#2) : Bool))))
                                  else (pure false)) : Bool)
                             then (pure true)
                             else
                               (do
                                 if ((((Sail.BitVec.castWidth (m := 2) (integer_subrange crm 3 2)) == 0b11#2) : Bool) : Bool)
                                 then
                                   (do
                                     let w__9 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                       (BitVec 64) )
                                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__9) == 1#1) : Bool))))
                                 else (pure false)))
                         else (pure false)))
                 else (pure false)) : Bool)
            then
              (do
                let w__15 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__15 -i 1)) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      if (w__17 : Bool)
      then
        (do
          let w__18 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__18 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  let w__20 ← (( do
    if (((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2))) : Bool) : Bool)
    then
      (do
        let w__19 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
        (pure ((((_get_PMSELR_EL0_Type_SEL w__19) != 0b11111#5) : Bool))))
    else (pure false) ) : SailME Unit Bool )
  if (w__20 : Bool)
  then
    (do
      let w__38 ← (( do
        if ((← do
             let w__21 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
             let w__22 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
             (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__21)) >b (w__22 -i 1)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__24 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__24.EL == EL1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         if ((← do
                              let w__25 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__25.EL == EL0) : Bool)))) : Bool)
                         then
                           (do
                             if ((← do
                                  if (((op2 == 2) : Bool) : Bool)
                                  then
                                    (do
                                      let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                        (BitVec 64) )
                                      let w__27 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                        (BitVec 64) )
                                      (pure (((((_get_PMUSERENR_EL0_Type_ER w__26) +++ (_get_PMUSERENR_EL0_Type_EN
                                              w__27)) != 0b00#2) : Bool))))
                                  else (pure false)) : Bool)
                             then (pure true)
                             else
                               (do
                                 if (((op2 == 1) : Bool) : Bool)
                                 then
                                   (do
                                     let w__29 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit
                                       (BitVec 64) )
                                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__29) == 1#1) : Bool))))
                                 else (pure false)))
                         else (pure false)))
                 else (pure false)) : Bool)
            then
              (do
                let w__35 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                let w__36 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__35)) >b (w__36 -i 1)) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      if (w__38 : Bool)
      then
        (do
          let w__39 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
          let w__40 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__39)) >b (w__40 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  let temp ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
  let w__41 ← (( do readReg PSTATE ) : SailME Unit ProcState )
  (AArch64_AutoGen_SysRegRead w__41.EL (integer_subrange op0 1 0) (integer_subrange op1 2 0)
    (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)
  if ((((((op0 == 3) && (crn == 10)) && (crm == 5)) && (op2 == 0)) && ((op1 == 0) || (op1 == 5))) : Bool)
  then
    (do
      let w__44 ← (( do
        if ((← do
             (HaveRME ())) : Bool)
        then
          (do
            let w__43 ← (( do readReg MPAMIDR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_MPAMIDR_EL1_Type_HAS_ALTSP w__43) == 1#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__44 : Bool)
      then
        (do
          let w__45 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
          let w__46 ← (( do (UsePrimarySpaceEL10 ()) ) : SailME Unit Bool )
          let w__47 : (BitVec 1) :=
            if ((! w__46) : Bool)
            then 1#1
            else 0#1
          (X_set t 64 (Sail.BitVec.updateSubrange w__45 54 54 w__47)))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 10)) && (crm == 5)) && (op2 == 0)) && (op1 == 4)) : Bool)
  then
    (do
      let w__50 ← (( do
        if ((← do
             (HaveRME ())) : Bool)
        then
          (do
            let w__49 ← (( do readReg MPAMIDR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_MPAMIDR_EL1_Type_HAS_ALTSP w__49) == 1#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__50 : Bool)
      then
        (do
          let w__51 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
          let w__52 ← (( do (UsePrimarySpaceEL2 ()) ) : SailME Unit Bool )
          let w__53 : (BitVec 1) :=
            if ((! w__52) : Bool)
            then 1#1
            else 0#1
          (X_set t 64 (Sail.BitVec.updateSubrange w__51 54 54 w__53)))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && (op2 == 7)) && (crm == 10)) : Bool)
  then
    (do
      let w__54 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
      let w__55 ← (( do (SPE_PMBIDR_P_Read ()) ) : SailME Unit (BitVec 1) )
      (X_set t 64 (Sail.BitVec.updateSubrange w__54 4 4 w__55)))
  else (pure (()))
  if ((((op0 == 3) && (crn == 9)) && (((((op1 == 3) && (op2 == 3)) && ((crm == 12) || (crm == 14))) || (((op1 == 3) && ((op2 == 1) || (op2 == 2))) && (crm == 12))) || (((op1 == 0) && ((op2 == 1) || (op2 == 2))) && (crm == 14)))) : Bool)
  then
    (do
      let mask ← (( do (PMUCounterMask ()) ) : SailME Unit (BitVec 64) )
      let w__56 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
      (X_set t 64 (w__56 &&& mask)))
  else (pure (()))
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2))) : Bool)
  then
    (do
      if ((op2 == 1) : Bool)
      then
        (do
          let w__66 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__58 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                               (pure (((w__58.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__59 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__59.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__62 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                     (pure ((((_get_PMSELR_EL0_Type_SEL w__62) != 0b11111#5) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__64 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                let w__65 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__64)) >b (w__65 -i 1)) : Bool))))
            else (pure false) ) : SailME Unit Bool )
          if (w__66 : Bool)
          then
            (do
              let w__67 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
              let w__68 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
              if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__67)) >b (w__68 -i 1)) : Bool)
              then
                (do
                  (X_set t 64 temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__69 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
              if (((_get_PMSELR_EL0_Type_SEL w__69) == 0b11111#5) : Bool)
              then
                (do
                  let w__70 ← (( do readReg PMCCFILTR_EL0 ) : SailME Unit (BitVec 64) )
                  (X_set t 64 w__70))
              else
                (do
                  let w__71 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                  let pmselr_el0 : Int := (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__71))
                  ArmFull.assert (pmselr_el0 <b 31) "sail-arm/sysregs.sail:335.38-335.39"
                  let w__72 ← (( do readReg PMEVTYPER_EL0 ) : SailME Unit (Vector (BitVec 64) 32)
                    )
                  (X_set t 64 (GetElem?.getElem! w__72 (Sail.Int.toNatChecked (pmselr_el0)))))))
      else (pure (()))
      if ((op2 == 2) : Bool)
      then
        (do
          let w__85 ← (( do
            if ((← do
                 if ((← do
                      let w__73 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                      let w__74 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
                      (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__73)) >b (w__74 -i 1)) : Bool)))) : Bool)
                 then
                   (do
                     let w__75 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                     (pure ((((_get_PMSELR_EL0_Type_SEL w__75) != 0b11111#5) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         if ((← do
                              let w__78 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__78.EL == EL0) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__79 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                             (pure (((w__79.EL == EL1) : Bool)))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__82 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                    let w__83 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit
                      Int )
                    (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__82)) >b (w__83 -i 1)) : Bool))))
                else (pure false)) ) : SailME Unit Bool )
          if (w__85 : Bool)
          then
            (do
              let w__86 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
              let w__87 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
              if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__86)) >b (w__87 -i 1)) : Bool)
              then
                (do
                  (X_set t 64 temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__88 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
              let pmselr_el0 : Int := (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__88))
              ArmFull.assert (pmselr_el0 <b 31) "sail-arm/sysregs.sail:350.38-350.39"
              let w__89 ← (( do readReg PMEVCNTR_EL0 ) : SailME Unit (Vector (BitVec 64) 32) )
              (X_set t 64 (GetElem?.getElem! w__89 (Sail.Int.toNatChecked (pmselr_el0))))))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then
    (do
      let w__90 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
      let w__91 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
      (X_set t 64 (Sail.BitVec.updateSubrange w__90 15 11 (integer_subrange w__91 4 0))))
  else (pure (()))
  if (((((op0 == 3) && (crn == 14)) && (op1 == 3)) && (((Sail.BitVec.castWidth (m := 2) (integer_subrange
             crm 3 2)) == 0b10#2) || (((Sail.BitVec.castWidth (m := 2) (integer_subrange crm 3 2)) == 0b11#2) && ((Sail.BitVec.castWidth (m := 5) ((integer_subrange
                 crm 1 0) +++ (integer_subrange op2 2 0))) != 0b11111#5)))) : Bool)
  then
    (do
      let w__101 ← (( do
        if ((← do
             (pure ((← do
                   let w__92 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
                   (pure ((((BitVec.toNat
                         ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__92 -i 1)) : Bool)))) && (((Sail.BitVec.castWidth (m := 5) ((integer_subrange
                       crm 1 0) +++ (integer_subrange op2 2 0))) != 0b11111#5) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     if ((← do
                          let w__95 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__95.EL == EL0) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__96 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                         (pure (((w__96.EL == EL1) : Bool)))))
                 else (pure false)) : Bool)
            then
              (do
                let w__99 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__99 -i 1)) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      if (w__101 : Bool)
      then
        (do
          let w__102 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__102 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (X_set t 64 temp)
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  if (((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then
        (do
          let w__103 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
          (X_set t 64 (Sail.BitVec.updateSubrange w__103 7 0 0b11111111#8))
          SailME.throw (() : Unit))
      else
        (do
          if ((crm == 9) : Bool)
          then
            (do
              let w__104 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
              let w__105 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailME Unit (BitVec 64) )
              (X_set t 64
                (Sail.BitVec.updateSubrange w__104 7 0 (Sail.BitVec.extractLsb w__105 7 0)))
              SailME.throw (() : Unit))
          else (pure (()))))
  else (pure (()))
  if (((((op0 == 2) && (op1 == 1)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then
        (do
          let w__106 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
          let w__107 ← (( do readReg __trcclaim_tags ) : SailME Unit (BitVec 32) )
          (X_set t 64 (Sail.BitVec.updateSubrange w__106 31 0 w__107))
          SailME.throw (() : Unit))
      else
        (do
          if ((crm == 9) : Bool)
          then
            (do
              let w__108 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
              let w__109 ← (( do readReg __trcclaim_tags ) : SailME Unit (BitVec 32) )
              (X_set t 64 (Sail.BitVec.updateSubrange w__108 31 0 w__109))
              SailME.throw (() : Unit))
          else (pure (()))))
  else (pure (()))
  if ((((((op0 == 3) && (op1 == 0)) && ((crn == (BitVec.toNat 0xA#4)) : Bool)) && (op2 == 0)) && (crm == 5)) : Bool)
  then
    (do
      let w__110 ← (( do (CurrentSecurityState ()) ) : SailME Unit SecurityState )
      if ((BEq.beq w__110 SS_Secure) : Bool)
      then
        (do
          let w__111 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
          let w__112 ← (( do (MPAM3_EL3_read ()) ) : SailME Unit (BitVec 64) )
          (X_set t 64
            (Sail.BitVec.updateSubrange w__111 60 60 (_get_MPAM3_EL3_Type_FORCE_NS w__112))))
      else (pure (())))
  else
    (do
      if ((((((op0 == 3) && ((crn == (BitVec.toNat 0xC#4)) : Bool)) && (op1 == 0)) && (op2 == 0)) && (crm == 1)) : Bool)
      then
        (do
          let w__113 ← (( do (getISR ()) ) : SailME Unit (BitVec 32) )
          (X_set t 64 (Sail.BitVec.zeroExtend w__113 64)))
      else
        (do
          if ((((((op0 == 3) && (crn == 0)) && (op1 == 1)) && ((op2 == 0) || (op2 == 2))) && (crm == 0)) : Bool)
          then
            (do
              if ((op2 == 0) : Bool)
              then
                (do
                  let w__114 ← (( do readReg CSSELR_EL1 ) : SailME Unit (BitVec 64) )
                  let w__115 ← (( do (CacheConfigRead (Sail.BitVec.extractLsb w__114 3 0)) ) :
                    SailME Unit (BitVec 64) )
                  (X_set t 64 w__115))
              else
                (do
                  let w__116 ← (( do readReg CSSELR_EL1 ) : SailME Unit (BitVec 64) )
                  let w__117 ← (( do (CacheConfigRead (Sail.BitVec.extractLsb w__116 3 0)) ) :
                    SailME Unit (BitVec 64) )
                  (X_set t 64 (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__117 63 32) 64))))
          else
            (do
              if ((((((op0 == 3) && (crn == 0)) && (op1 == 3)) && (op2 == 7)) && (crm == 0)) : Bool)
              then
                (do
                  let w__118 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  if ((w__118.EL == EL0) : Bool)
                  then
                    (do
                      let w__119 ← (( do (IsInHost ()) ) : SailME Unit Bool )
                      if (w__119 : Bool)
                      then
                        (do
                          let w__120 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__121 ← (( do readReg SCTLR_EL2 ) : SailME Unit (BitVec 64) )
                          let w__122 : (BitVec 1) :=
                            if (((_get_SCTLR_EL2_Type_DZE w__121) == 0#1) : Bool)
                            then 1#1
                            else 0#1
                          (X_set t 64 (Sail.BitVec.updateSubrange w__120 4 4 w__122)))
                      else
                        (do
                          let w__123 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__128 ← (( do
                            if ((← do
                                 let w__124 ← (( do readReg SCTLR_EL1 ) : SailME Unit (BitVec 64)
                                   )
                                 (pure ((((_get_SCTLR_EL1_Type_DZE w__124) == 0#1) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__126 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64)
                                      )
                                    (pure ((((_get_HCR_EL2_Type_TDZ w__126) == 1#1) : Bool))))
                                else (pure false)) ) : SailME Unit Bool )
                          let w__129 : (BitVec 1) :=
                            if (w__128 : Bool)
                            then 1#1
                            else 0#1
                          (X_set t 64 (Sail.BitVec.updateSubrange w__123 4 4 w__129))))
                  else
                    (do
                      let w__130 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                      if ((w__130.EL == EL1) : Bool)
                      then
                        (do
                          let w__131 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__134 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__133 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                                (pure ((((_get_HCR_EL2_Type_TDZ w__133) == 1#1) : Bool))))
                            else (pure false) ) : SailME Unit Bool )
                          let w__135 : (BitVec 1) :=
                            if (w__134 : Bool)
                            then 1#1
                            else 0#1
                          (X_set t 64 (Sail.BitVec.updateSubrange w__131 4 4 w__135)))
                      else (pure (()))))
              else
                (do
                  let w__136 ← (( do (AArch64_CheckNVCondsIfCurrentEL op0 op1 crn crm op2) ) :
                    SailME Unit Bool )
                  if (w__136 : Bool)
                  then
                    (do
                      let w__137 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                      (X_set t 64 (Sail.BitVec.updateSubrange w__137 3 2 0b10#2)))
                  else (pure (()))
                  if ((((((op0 == 3) && (crn == 2)) && (crm == 4)) && (op1 == 3)) && ((op2 == 0) || (op2 == 1))) : Bool)
                  then
                    (do
                      let w__140 ← (( do
                        if ((op2 == 0) : Bool)
                        then
                          (do
                            (genRandomNum false))
                        else
                          (do
                            (genRandomNum true)) ) : SailME Unit (BitVec 64) )
                      (X_set t 64 w__140))
                  else (pure (()))
                  if (((((op0 == 2) && (op1 == 1)) && (crn == 8)) && ((op2 == 0) || ((op2 == 1) || ((op2 == 2) || ((op2 == 4) || ((op2 == 5) || (op2 == 6))))))) : Bool)
                  then
                    (do
                      let w__141 ← (( do readReg BRBFCR_EL1 ) : SailME Unit (BitVec 64) )
                      let recordIdx : Int :=
                        (BitVec.toNat
                          (((_get_BRBFCR_EL1_Type_BANK w__141) +++ (BitVec.setWidth 1 (BitVec.join1 [(integer_access
                                  op2 2)]))) +++ (integer_subrange crm 3 0)))
                      let w__142 ← (( do (GetBRBENumRecords ()) ) : SailME Unit Int )
                      if ((recordIdx <b w__142) : Bool)
                      then
                        (do
                          if (((op2 == 0) || (op2 == 4)) : Bool)
                          then
                            (do
                              ArmFull.assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "sail-arm/sysregs.sail:443.70-443.71"
                              let w__143 ← (( do readReg Records_INF ) : SailME Unit
                                (Vector (BitVec 64) 64) )
                              (X_set t 64
                                (GetElem?.getElem! w__143 (Sail.Int.toNatChecked (recordIdx)))))
                          else (pure (()))
                          if (((op2 == 1) || (op2 == 5)) : Bool)
                          then
                            (do
                              ArmFull.assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "sail-arm/sysregs.sail:447.70-447.71"
                              let w__144 ← (( do readReg Records_SRC ) : SailME Unit
                                (Vector (BitVec 64) 64) )
                              (X_set t 64
                                (GetElem?.getElem! w__144 (Sail.Int.toNatChecked (recordIdx)))))
                          else (pure (()))
                          if (((op2 == 2) || (op2 == 6)) : Bool)
                          then
                            (do
                              ArmFull.assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "sail-arm/sysregs.sail:451.70-451.71"
                              let w__145 ← (( do readReg Records_TGT ) : SailME Unit
                                (Vector (BitVec 64) 64) )
                              (X_set t 64
                                (GetElem?.getElem! w__145 (Sail.Int.toNatChecked (recordIdx)))))
                          else (pure (())))
                      else
                        (do
                          (X_set t 64 (Zeros (n := 64)))))
                  else (pure (()))
                  if ((((((op0 == 3) && (crn == 5)) && (op1 == 0)) && (op2 == 0)) && (crm == 4)) : Bool)
                  then
                    (do
                      let w__149 ← (( do
                        if ((← do
                             let w__146 ← (( do readReg ERRIDR_EL1 ) : SailME Unit (BitVec 64) )
                             (pure ((((BitVec.toNat (_get_ERRIDR_EL1_Type_NUM w__146)) == (BitVec.toNat
                                   0x0#4)) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__147 ← (( do readReg ERRSELR_EL1 ) : SailME Unit (BitVec 64) )
                            let w__148 ← (( do readReg ERRIDR_EL1 ) : SailME Unit (BitVec 64) )
                            (pure ((((BitVec.toNat (_get_ERRSELR_EL1_Type_SEL w__147)) ≥b (BitVec.toNat
                                  (_get_ERRIDR_EL1_Type_NUM w__148))) : Bool)))) ) : SailME Unit
                        Bool )
                      if (w__149 : Bool)
                      then
                        (do
                          (X_set t 64 (Zeros (n := 64))))
                      else
                        (do
                          let w__150 ← (( do readReg ERRSELR_EL1 ) : SailME Unit (BitVec 64) )
                          let index : Int := (BitVec.toNat (_get_ERRSELR_EL1_Type_SEL w__150))
                          ArmFull.assert ((0 ≤b index) && (index <b 4)) "sail-arm/sysregs.sail:464.57-464.58"
                          let w__151 ← (( do readReg ERRnFR ) : SailME Unit (Vector (BitVec 64) 4)
                            )
                          (X_set t 64 (GetElem?.getElem! w__151 (Sail.Int.toNatChecked (index))))))
                  else (pure (()))
                  if ((((((op0 == 2) && (crn == 7)) && (op1 == 0)) && (op2 == 6)) && (crm == 14)) : Bool)
                  then
                    (do
                      if ((HaveEL EL3) : Bool)
                      then
                        (do
                          let w__152 ← (( do (ExternalInvasiveDebugEnabled ()) ) : SailME Unit
                            Bool )
                          if (w__152 : Bool)
                          then
                            (do
                              let w__153 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__153 1 0 0b11#2)))
                          else
                            (do
                              let w__154 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__154 1 0 0b10#2)))
                          let w__155 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          (X_set t 64 (Sail.BitVec.updateSubrange w__155 3 2 0b11#2))
                          let w__156 ← (( do (ExternalSecureInvasiveDebugEnabled ()) ) : SailME
                            Unit Bool )
                          if (w__156 : Bool)
                          then
                            (do
                              let w__157 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__157 5 4 0b11#2)))
                          else
                            (do
                              let w__158 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__158 5 4 0b10#2)))
                          let w__159 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__160 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          (X_set t 64
                            (Sail.BitVec.updateSubrange w__159 7 6
                              (Sail.BitVec.extractLsb w__160 5 4))))
                      else (pure (())))
                  else
                    (do
                      if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 5)) : Bool)
                      then
                        (do
                          let w__161 ← (( do (DBGDSCRint_read ()) ) : SailME Unit (BitVec 32) )
                          (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull w__161 0#1))
                          let w__162 ← (( do readReg MDCCSR_EL0 ) : SailME Unit (BitVec 64) )
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__162 30 30 0#1)
                          let w__163 ← (( do (DBGDSCRext_read ()) ) : SailME Unit (BitVec 32) )
                          (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull w__163 0#1))
                          let w__164 ← (( do (EDSCR_read ()) ) : SailME Unit (BitVec 32) )
                          (EDSCR_write (_update_EDSCR_Type_RXfull w__164 0#1)))
                      else (pure (()))
                      if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 4)) : Bool)
                      then
                        (do
                          let w__165 ← (( do (DBGDSCRint_read ()) ) : SailME Unit (BitVec 32) )
                          (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull w__165 0#1))
                          let w__166 ← (( do readReg MDCCSR_EL0 ) : SailME Unit (BitVec 64) )
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__166 30 30 0#1)
                          let w__167 ← (( do (DBGDSCRext_read ()) ) : SailME Unit (BitVec 32) )
                          (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull w__167 0#1))
                          let w__168 ← (( do (EDSCR_read ()) ) : SailME Unit (BitVec 32) )
                          (EDSCR_write (_update_EDSCR_Type_RXfull w__168 0#1))
                          let w__169 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__170 ← (( do readReg DBGDTRTX_EL0 ) : SailME Unit (BitVec 64) )
                          (X_set t 64 (set_slice 32 w__169 32 (BitVec.slice w__170 0 32)))
                          let w__171 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          let w__172 ← (( do readReg DBGDTRRX_EL0 ) : SailME Unit (BitVec 64) )
                          (X_set t 64 (set_slice 32 w__171 0 (BitVec.slice w__172 0 32))))
                      else (pure (()))
                      if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
                      then
                        (do
                          let w__175 ← (( do
                            if ((← do
                                 let w__173 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                                 (pure (((w__173.EL == EL2) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__174 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                                (pure (((w__174.EL == EL3) : Bool)))) ) : SailME Unit Bool )
                          if (w__175 : Bool)
                          then
                            (do
                              let w__176 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__176 26 24 0b000#3)))
                          else (pure (())))
                      else (pure (()))
                      if ((((((op0 == 3) && (crn == 4)) && (op1 == 0)) && (op2 == 0)) && (crm == 6)) : Bool)
                      then
                        (do
                          let w__177 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                          (X_set t 64 (Sail.BitVec.updateSubrange w__177 2 0 0b000#3)))
                      else (pure (()))
                      if ((((((op0 == 3) && (crn == 1)) && (op1 == 4)) && (op2 == 0)) && (crm == 1)) : Bool)
                      then
                        (do
                          let w__180 ← (( do
                            if ((← do
                                 let w__178 ← (( do (ELUsingAArch32 EL1) ) : SailME Unit Bool )
                                 (pure (((! w__178) : Bool)))) : Bool)
                            then
                              (do
                                let w__179 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                                (pure (((w__179.EL != EL1) : Bool))))
                            else (pure false) ) : SailME Unit Bool )
                          if (w__180 : Bool)
                          then
                            (do
                              let w__181 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__181 31 31 1#1)))
                          else (pure (())))
                      else (pure (()))
                      if ((((((op0 == 3) && (crn == 12)) && (op1 == 6)) && (op2 == 2)) && (crm == 0)) : Bool)
                      then
                        (do
                          let w__182 ← (( do readReg ID_AA64PFR0_EL1 ) : SailME Unit (BitVec 64) )
                          if (((_get_ID_AA64PFR0_EL1_Type_EL3 w__182) == 0b0001#4) : Bool)
                          then
                            (do
                              let w__183 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
                              (X_set t 64 (Sail.BitVec.updateSubrange w__183 0 0 1#1)))
                          else (pure (())))
                      else (pure (())))))))


end ArmFull.Functions
