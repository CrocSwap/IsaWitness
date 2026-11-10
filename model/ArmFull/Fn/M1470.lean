import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0053
import ArmFull.Fn.M0059
import ArmFull.Fn.M0066
import ArmFull.Fn.M0070
import ArmFull.Fn.M0071
import ArmFull.Fn.M0072
import ArmFull.Fn.M0074
import ArmFull.Fn.M0075
import ArmFull.Fn.M0076
import ArmFull.Fn.M0080
import ArmFull.Fn.M0087
import ArmFull.Fn.M0116
import ArmFull.Fn.M0139
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0159
import ArmFull.Fn.M0174
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0189
import ArmFull.Fn.M0244
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
def AArch64_SysRegWrite (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let n ← (( do (undefined_int_at (← occLabel 2897) ()) ) : SailME Unit Int )
  let tempxt ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
  let tempxt : (BitVec 64) :=
    if (((((op0 == 2) && (crn == 0)) && (op1 == 0)) && (op2 == 5)) : Bool)
    then
      (let tempxt : (BitVec 64) :=
        (BitVec.update tempxt 8 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tempxt 7)]))))
      (BitVec.update tempxt 6 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tempxt 5)])))))
    else tempxt
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 4)) && (crm == 12)) : Bool)
    then
      (do
        let w__0 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 19 (Bit (_get_ICV_CTLR_EL1_Type_ExtRange w__0))) : (BitVec 64))
        let w__1 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((Sail.BitVec.updateSubrange tempxt 13 11 (_get_ICV_CTLR_EL1_Type_IDbits w__1)) : (BitVec 64))
        let w__2 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((Sail.BitVec.updateSubrange tempxt 10 8 (_get_ICV_CTLR_EL1_Type_PRIbits w__2)) : (BitVec 64))
        let w__3 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 15 (Bit (_get_ICV_CTLR_EL1_Type_A3V w__3))) : (BitVec 64))
        let w__4 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 14 (Bit (_get_ICV_CTLR_EL1_Type_SEIS w__4))) : (BitVec 64))
        (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 6)) && (op2 == 4)) && (crm == 12)) : Bool)
    then
      (do
        let w__5 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 19 (Bit (_get_ICC_CTLR_EL3_Type_ExtRange w__5))) : (BitVec 64))
        let w__6 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((Sail.BitVec.updateSubrange tempxt 13 11 (_get_ICC_CTLR_EL3_Type_IDbits w__6)) : (BitVec 64))
        let w__7 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((Sail.BitVec.updateSubrange tempxt 10 8 (_get_ICC_CTLR_EL3_Type_PRIbits w__7)) : (BitVec 64))
        let w__8 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 17 (Bit (_get_ICC_CTLR_EL3_Type_nDS w__8))) : (BitVec 64))
        let w__9 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 15 (Bit (_get_ICC_CTLR_EL3_Type_A3V w__9))) : (BitVec 64))
        let w__10 ← (( do readReg ICC_CTLR_EL3 ) : SailME Unit (BitVec 64) )
        let tempxt :=
          ((BitVec.update tempxt 14 (Bit (_get_ICC_CTLR_EL3_Type_SEIS w__10))) : (BitVec 64))
        (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
    then
      (do
        let w__13 ← (( do
          if ((← do
               let w__11 ← (( do readReg PSTATE ) : SailME Unit ProcState )
               (pure (((w__11.EL == EL2) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__12 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              (pure (((w__12.EL == EL3) : Bool)))) ) : SailME Unit Bool )
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
            let tempxt ← (( do
              if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 23 21)) <b (6 -i (BitVec.toNat
                       (_get_ICH_VTR_EL2_Type_PREbits w__14)))) : Bool)
              then
                (do
                  let w__15 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                  let tempxt :=
                    ((Sail.BitVec.updateSubrange tempxt 23 21
                      (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__15)))
                        2 0)) : (BitVec 64))
                  (pure (tempxt)))
              else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
            let w__16 ← (( do (CurrentSecurityState ()) ) : SailME Unit SecurityState )
            let tempxt ← (( do
              if ((BEq.beq w__16 SS_Secure) : Bool)
              then
                (do
                  let w__17 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                  if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (6 -i (BitVec.toNat
                           (_get_ICH_VTR_EL2_Type_PREbits w__17)))) : Bool)
                  then
                    (do
                      let w__18 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                      let tempxt :=
                        ((Sail.BitVec.updateSubrange tempxt 20 18
                          (integer_subrange
                            (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__18))) 2 0)) : (BitVec 64))
                      (pure (tempxt)))
                  else (pure (tempxt)))
              else
                (do
                  let w__19 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                  if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (7 -i (BitVec.toNat
                           (_get_ICH_VTR_EL2_Type_PREbits w__19)))) : Bool)
                  then
                    (do
                      let w__20 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                      let tempxt :=
                        ((Sail.BitVec.updateSubrange tempxt 20 18
                          (integer_subrange
                            (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__20))) 2 0)) : (BitVec 64))
                      (pure (tempxt)))
                  else (pure (tempxt))) ) : SailME Unit (BitVec 64) )
            let w__21 ← (( do readReg ICC_SRE_EL1_NS ) : SailME Unit (BitVec 64) )
            let tempxt : (BitVec 64) :=
              if (((_get_ICC_SRE_EL1_Type_SRE w__21) == 1#1) : Bool)
              then (Sail.BitVec.updateSubrange tempxt 3 2 0b10#2)
              else tempxt
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 8)) : Bool)
    then
      (do
        let w__22 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
        if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat
                 (_get_ICH_VTR_EL2_Type_PREbits w__22)))) : Bool)
        then
          (do
            let w__23 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
            let tempxt :=
              ((Sail.BitVec.updateSubrange tempxt 2 0
                (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__23))) 2 0)) : (BitVec 64))
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 12)) : Bool)
    then
      (do
        let w__24 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
        if (((_get_ICV_CTLR_EL1_Type_CBPR w__24) == 0#1) : Bool)
        then
          (do
            let w__25 ← (( do (CurrentSecurityState ()) ) : SailME Unit SecurityState )
            if ((BEq.beq w__25 SS_Secure) : Bool)
            then
              (do
                let w__26 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat
                         (_get_ICH_VTR_EL2_Type_PREbits w__26)))) : Bool)
                then
                  (do
                    let w__27 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                    let tempxt :=
                      ((Sail.BitVec.updateSubrange tempxt 2 0
                        (integer_subrange
                          (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__27))) 2 0)) : (BitVec 64))
                    (pure (tempxt)))
                else (pure (tempxt)))
            else
              (do
                let w__28 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (7 -i (BitVec.toNat
                         (_get_ICH_VTR_EL2_Type_PREbits w__28)))) : Bool)
                then
                  (do
                    let w__29 ← (( do readReg ICH_VTR_EL2 ) : SailME Unit (BitVec 64) )
                    let tempxt :=
                      ((Sail.BitVec.updateSubrange tempxt 2 0
                        (integer_subrange
                          (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits w__29))) 2 0)) : (BitVec 64))
                    (pure (tempxt)))
                else (pure (tempxt))))
        else
          (do
            let w__30 ← (( do readReg ICV_BPR1_EL1 ) : SailME Unit (BitVec 64) )
            let tempxt :=
              ((Sail.BitVec.updateSubrange tempxt 2 0 (_get_ICV_BPR1_EL1_Type_BinaryPoint w__30)) : (BitVec 64))
            (pure (tempxt))))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
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
          let w__31 ← (( do readReg AMCGCR_EL0 ) : SailME Unit (BitVec 64) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC w__31))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else
        (do
          if ((((Sail.BitVec.castWidth (m := 3) (integer_subrange crm 3 1)) == 0b110#3) || ((Sail.BitVec.castWidth (m := 3) (integer_subrange
                   crm 3 1)) == 0b111#3)) : Bool)
          then
            (do
              let w__32 ← (( do readReg AMCGCR_EL0 ) : SailME Unit (BitVec 64) )
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC w__32))) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))))
  else (pure (()))
  let mask ← (( do (PMUCounterMask ()) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 3)) && ((crm == 12) || (crm == 14))) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((crm == 12) : Bool)
          then
            (do
              let w__33 ← (( do readReg PMOVSSET_EL0 ) : SailME Unit (BitVec 64) )
              let tempxt := ((w__33 &&& (Complement.complement (tempxt &&& mask))) : (BitVec 64))
              (pure (tempxt)))
          else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
        if ((crm == 14) : Bool)
        then
          (do
            let w__34 ← (( do readReg PMOVSSET_EL0 ) : SailME Unit (BitVec 64) )
            let tempxt := ((w__34 ||| (tempxt &&& mask)) : (BitVec 64))
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && ((op2 == 1) || (op2 == 2))) && (crm == 12)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((op2 == 2) : Bool)
          then
            (do
              let w__35 ← (( do readReg PMCNTENSET_EL0 ) : SailME Unit (BitVec 64) )
              let tempxt := ((w__35 &&& (Complement.complement (tempxt &&& mask))) : (BitVec 64))
              (pure (tempxt)))
          else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
        if ((op2 == 1) : Bool)
        then
          (do
            let w__36 ← (( do readReg PMCNTENSET_EL0 ) : SailME Unit (BitVec 64) )
            let tempxt := ((w__36 ||| (tempxt &&& mask)) : (BitVec 64))
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && ((op2 == 1) || (op2 == 2))) && (crm == 14)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((op2 == 2) : Bool)
          then
            (do
              let w__37 ← (( do readReg PMINTENSET_EL1 ) : SailME Unit (BitVec 64) )
              let tempxt := ((w__37 &&& (Complement.complement (tempxt &&& mask))) : (BitVec 64))
              (pure (tempxt)))
          else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
        if ((op2 == 1) : Bool)
        then
          (do
            let w__38 ← (( do readReg PMINTENSET_EL1 ) : SailME Unit (BitVec 64) )
            let tempxt := ((w__38 ||| (tempxt &&& mask)) : (BitVec 64))
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then
    (do
      let w__40 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tempxt 3)])) == 1#1) : Bool) : Bool)
        then
          (do
            let w__39 ← (( do readReg PMCR_EL0 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_PMCR_EL0_Type_D w__39) == 0#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__40 : Bool)
      then
        (do
          writeReg __clock_divider 63)
      else (pure (())))
  else (pure (()))
  if (((((op0 == 3) && (crn == 14)) && (op1 == 3)) && (((Sail.BitVec.castWidth (m := 2) (integer_subrange
             crm 3 2)) == 0b10#2) || (((Sail.BitVec.castWidth (m := 2) (integer_subrange crm 3 2)) == 0b11#2) && ((Sail.BitVec.castWidth (m := 5) ((integer_subrange
                 crm 1 0) +++ (integer_subrange op2 2 0))) != 0b11111#5)))) : Bool)
  then
    (do
      let w__52 ← (( do
        if ((← do
             (pure ((← do
                   let w__41 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
                   (pure ((((BitVec.toNat
                         ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__41 -i 1)) : Bool)))) && (((Sail.BitVec.castWidth (m := 5) ((integer_subrange
                       crm 1 0) +++ (integer_subrange op2 2 0))) != 0b11111#5) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__44 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                               (pure (((w__44.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__45 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__45.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__48 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit (BitVec 64) )
                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__48) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__50 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__50 -i 1)) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      if (w__52 : Bool)
      then
        (do
          let w__53 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b (w__53 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  let w__57 ← (( do
    if ((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) : Bool) : Bool)
    then
      (do
        if (((op2 == 2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((op2 == 1) : Bool) : Bool)
            then
              (do
                let w__54 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                (pure ((((_get_PMSELR_EL0_Type_SEL w__54) != 0b11111#5) : Bool))))
            else (pure false)))
    else (pure false) ) : SailME Unit Bool )
  if (w__57 : Bool)
  then
    (do
      let w__72 ← (( do
        if ((← do
             if ((← do
                  let w__58 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                  let w__59 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
                  (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__58)) >b (w__59 -i 1)) : Bool)))) : Bool)
             then
               (do
                 let w__60 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                 (pure ((((_get_PMSELR_EL0_Type_SEL w__60) != 0b11111#5) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__63 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                               (pure (((w__63.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__64 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__64.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__67 ← (( do readReg PMUSERENR_EL0 ) : SailME Unit (BitVec 64) )
                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__67) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__69 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
                let w__70 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailME Unit Int )
                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__69)) >b (w__70 -i 1)) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      if (w__72 : Bool)
      then
        (do
          let w__73 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
          let w__74 ← (( do (GetNumEventCounters ()) ) : SailME Unit Int )
          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__73)) >b (w__74 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  let tempxt ← (( do
    if (((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((crm == 8) : Bool)
          then
            (do
              let w__75 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailME Unit (BitVec 64) )
              let tempxt :=
                ((Sail.BitVec.updateSubrange tempxt 7 0
                  ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__75 7 0)) ||| (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                      tempxt 7 0)))) : (BitVec 64))
              (pure (tempxt)))
          else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
        if ((crm == 9) : Bool)
        then
          (do
            let w__76 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailME Unit (BitVec 64) )
            let tempxt :=
              ((Sail.BitVec.updateSubrange tempxt 7 0
                ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__76 7 0)) &&& (Sail.BitVec.castWidth (m := 8) (Complement.complement
                    (Sail.BitVec.extractLsb tempxt 7 0))))) : (BitVec 64))
            (pure (tempxt)))
        else (pure (tempxt)))
    else (pure (tempxt)) ) : SailME Unit (BitVec 64) )
  let tempxt2 ← (( do (undefined_bitvector_at (← occLabel 2898) 64) ) : SailME Unit (BitVec 64)
    )
  let restore_xt ← (( do (undefined_bool_at (← occLabel 2899) ()) ) : SailME Unit Bool )
  let w__77 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
  let (restore_xt, tempxt2) ← (( do
    if ((tempxt != w__77) : Bool)
    then
      (do
        let w__78 ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
        let tempxt2 := (w__78 : (BitVec 64))
        (X_set t 64 tempxt)
        let restore_xt : Bool := true
        (pure ((restore_xt, tempxt2))))
    else
      (let restore_xt : Bool := false
      (pure ((restore_xt, tempxt2)))) ) : SailME Unit (Bool × (BitVec 64)) )
  let w__79 ← (( do readReg PSTATE ) : SailME Unit ProcState )
  (AArch64_AutoGen_SysRegWrite w__79.EL (integer_subrange op0 1 0) (integer_subrange op1 2 0)
    (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)
  if (restore_xt : Bool)
  then
    (do
      (X_set t 64 tempxt2))
  else (pure (()))
  if ((((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) && (crm == 8)) : Bool)
  then
    (do
      let w__80 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__80 7 0
        (Sail.BitVec.extractLsb tempxt 7 0)))
  else (pure (()))
  if ((((((crm == 0) && (crn == 1)) && (op0 == 2)) && (op1 == 0)) && (op2 == 4)) : Bool)
  then
    (do
      let w__83 ← (( do
        if ((← do
             let w__81 ← (( do readReg OSLSR_EL1 ) : SailME Unit (BitVec 64) )
             (pure ((((_get_OSLSR_EL1_Type_OSLK w__81) == 1#1) : Bool)))) : Bool)
        then
          (do
            let w__82 ← (( do readReg OSLAR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_OSLAR_EL1_Type_OSLK w__82) == 0#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__83 : Bool)
      then
        (do
          (CheckOSUnlockCatch ()))
      else (pure (()))
      let w__84 ← (( do readReg OSLSR_EL1 ) : SailME Unit (BitVec 64) )
      let w__85 ← (( do readReg OSLAR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__84 1 1 (_get_OSLAR_EL1_Type_OSLK w__85))
      let w__86 ← (( do readReg EDPRSR ) : SailME Unit (BitVec 32) )
      let w__87 ← (( do readReg OSLSR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg EDPRSR (Sail.BitVec.updateSubrange w__86 5 5 (_get_OSLSR_EL1_Type_OSLK w__87))
      let w__88 ← (( do (DBGOSLSR_read ()) ) : SailME Unit (BitVec 32) )
      let w__89 ← (( do readReg OSLSR_EL1 ) : SailME Unit (BitVec 64) )
      (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK w__88 (_get_OSLSR_EL1_Type_OSLK w__89))))
  else (pure (()))
  if (((((op0 == 2) && (op1 == 1)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then
        (do
          let w__90 ← (( do readReg __trcclaim_tags ) : SailME Unit (BitVec 32) )
          writeReg __trcclaim_tags (w__90 ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
              tempxt 31 0)))
          SailME.throw (() : Unit))
      else
        (do
          if ((crm == 9) : Bool)
          then
            (do
              let w__91 ← (( do readReg __trcclaim_tags ) : SailME Unit (BitVec 32) )
              writeReg __trcclaim_tags (w__91 &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
                  (Sail.BitVec.extractLsb tempxt 31 0))))
              SailME.throw (() : Unit))
          else (pure (()))))
  else (pure (()))
  if (((((((op0 == 3) && ((crn == (BitVec.toNat 0xC#4)) : Bool)) && (((op1 == 6) || (op1 == 4)) || (op1 == 0))) && (op2 == 2)) && (crm == 0)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             tempxt 1)])) == 1#1)) : Bool)
  then
    (do
      (TakeReset false))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 3)) && ((crm == 12) || (crm == 14))) : Bool)
  then
    (do
      if ((crm == 12) : Bool)
      then
        (do
          writeReg PMOVSSET_EL0 (Mk_PMOVSSET_EL0_Type tempxt))
      else (pure (()))
      if ((crm == 14) : Bool)
      then
        (do
          writeReg PMOVSCLR_EL0 (Mk_PMOVSCLR_EL0_Type tempxt))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && ((op2 == 1) || (op2 == 2))) && (crm == 12)) : Bool)
  then
    (do
      if ((op2 == 2) : Bool)
      then
        (do
          writeReg PMCNTENSET_EL0 (Mk_PMCNTENSET_EL0_Type tempxt))
      else (pure (()))
      if ((op2 == 1) : Bool)
      then
        (do
          writeReg PMCNTENCLR_EL0 (Mk_PMCNTENCLR_EL0_Type tempxt))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && ((op2 == 1) || (op2 == 2))) && (crm == 14)) : Bool)
  then
    (do
      if ((op2 == 2) : Bool)
      then
        (do
          writeReg PMINTENSET_EL1 (Mk_PMINTENSET_EL1_Type tempxt))
      else (pure (()))
      if ((op2 == 1) : Bool)
      then
        (do
          writeReg PMINTENCLR_EL1 (Mk_PMINTENCLR_EL1_Type tempxt))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tempxt 2)])) == 1#1) : Bool)
      then
        (do
          writeReg PMCCNTR_EL0 (Mk_PMCCNTR_EL0_Type (Zeros (n := 64))))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tempxt 1)])) == 1#1) : Bool)
      then
        (do
          (AArch64_ClearEventCounters ()))
      else (pure (())))
  else (pure (()))
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2))) : Bool)
  then
    (do
      if ((op2 == 1) : Bool)
      then
        (do
          let w__92 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
          if (((_get_PMSELR_EL0_Type_SEL w__92) == 0b11111#5) : Bool)
          then
            (do
              writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt)))
          else
            (do
              let w__93 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
              let pmselr_el0 : Int := (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__93))
              ArmFull.assert (pmselr_el0 <b 31) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:748.38-748.39"
              let w__94 ← (( do readReg PMEVTYPER_EL0 ) : SailME Unit (Vector (BitVec 64) 32) )
              writeReg PMEVTYPER_EL0 (vectorUpdate w__94 (Sail.Int.toNatChecked (pmselr_el0))
                (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt)))))
      else (pure (()))
      if ((op2 == 2) : Bool)
      then
        (do
          let w__95 ← (( do readReg PMSELR_EL0 ) : SailME Unit (BitVec 64) )
          let pmselr_el0 : Int := (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__95))
          ArmFull.assert (pmselr_el0 <b 31) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:754.34-754.35"
          let w__96 ← (( do readReg PMEVCNTR_EL0 ) : SailME Unit (Vector (BitVec 64) 32) )
          writeReg PMEVCNTR_EL0 (vectorUpdate w__96 (Sail.Int.toNatChecked (pmselr_el0)) tempxt))
      else (pure (())))
  else (pure (()))
  if (((((op0 == 3) && (op1 == 3)) && (crn == 14)) && ((Sail.BitVec.castWidth (m := 2) (integer_subrange
           crm 3 2)) == 0b11#2)) : Bool)
  then
    (do
      let index : Int := (BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)))
      if ((index == 31) : Bool)
      then
        (do
          writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt)))
      else
        (do
          let w__97 ← (( do readReg PMEVTYPER_EL0 ) : SailME Unit (Vector (BitVec 64) 32) )
          writeReg PMEVTYPER_EL0 (vectorUpdate w__97 (Sail.Int.toNatChecked (index))
            (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt)))))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 4)) && (crm == 12)) : Bool)
  then
    (do
      (AArch64_PMUSwIncrement (Sail.BitVec.extractLsb tempxt 31 0)))
  else (pure (()))
  if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 5)) : Bool)
  then
    (do
      let w__98 ← (( do (DBGDSCRint_read ()) ) : SailME Unit (BitVec 32) )
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull w__98 1#1))
      let w__99 ← (( do readReg MDCCSR_EL0 ) : SailME Unit (BitVec 64) )
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__99 29 29 1#1)
      let w__100 ← (( do (DBGDSCRext_read ()) ) : SailME Unit (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull w__100 1#1))
      let w__101 ← (( do (EDSCR_read ()) ) : SailME Unit (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TXfull w__101 1#1)))
  else (pure (()))
  if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 4)) : Bool)
  then
    (do
      let w__102 ← (( do (DBGDSCRint_read ()) ) : SailME Unit (BitVec 32) )
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull w__102 1#1))
      let w__103 ← (( do readReg MDCCSR_EL0 ) : SailME Unit (BitVec 64) )
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__103 29 29 1#1)
      let w__104 ← (( do (DBGDSCRext_read ()) ) : SailME Unit (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull w__104 1#1))
      let w__105 ← (( do (EDSCR_read ()) ) : SailME Unit (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TXfull w__105 1#1))
      let w__106 ← (( do readReg DBGDTRTX_EL0 ) : SailME Unit (BitVec 64) )
      let w__107 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailME Unit (BitVec 64) )
      writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__106 31 0 (BitVec.slice w__107 0 32))
      let w__108 ← (( do readReg DBGDTRRX_EL0 ) : SailME Unit (BitVec 64) )
      let w__109 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailME Unit (BitVec 64) )
      writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__108 31 0 (BitVec.slice w__109 32 32)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
  then
    (do
      let w__110 ← (( do readReg ICV_PMR_EL1 ) : SailME Unit (BitVec 64) )
      let w__111 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange w__110 7 0
        (_get_ICH_VMCR_EL2_Type_VPMR w__111))
      let w__112 ← (( do readReg ICV_BPR0_EL1 ) : SailME Unit (BitVec 64) )
      let w__113 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange w__112 2 0
        (_get_ICH_VMCR_EL2_Type_VBPR0 w__113))
      let w__114 ← (( do readReg ICV_BPR1_EL1 ) : SailME Unit (BitVec 64) )
      let w__115 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange w__114 2 0
        (_get_ICH_VMCR_EL2_Type_VBPR1 w__115))
      let w__116 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailME Unit (BitVec 64) )
      let w__117 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__116 0 0
        (_get_ICH_VMCR_EL2_Type_VENG0 w__117))
      let w__118 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailME Unit (BitVec 64) )
      let w__119 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange w__118 0 0
        (_get_ICH_VMCR_EL2_Type_VENG1 w__119))
      let w__120 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
      let w__121 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__120 1 1
        (_get_ICH_VMCR_EL2_Type_VEOIM w__121))
      let w__122 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
      let w__123 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__122 0 0
        (_get_ICH_VMCR_EL2_Type_VCBPR w__123)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 4)) && (op1 == 0)) && (op2 == 0)) && (crm == 6)) : Bool)
  then
    (do
      let w__124 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__125 ← (( do readReg ICV_PMR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__124 31 24
        (_get_ICV_PMR_EL1_Type_Priority w__125)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 8)) : Bool)
  then
    (do
      let w__126 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__127 ← (( do readReg ICV_BPR0_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__126 23 21
        (_get_ICV_BPR0_EL1_Type_BinaryPoint w__127)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 12)) : Bool)
  then
    (do
      let w__128 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__129 ← (( do readReg ICV_BPR1_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__128 20 18
        (_get_ICV_BPR1_EL1_Type_BinaryPoint w__129)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 4)) && (crm == 12)) : Bool)
  then
    (do
      let w__130 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__131 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__130 9 9
        (_get_ICV_CTLR_EL1_Type_EOImode w__131))
      let w__132 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__133 ← (( do readReg ICV_CTLR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__132 4 4
        (_get_ICV_CTLR_EL1_Type_CBPR w__133)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 6)) && (crm == 12)) : Bool)
  then
    (do
      let w__134 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__135 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__134 0 0
        (_get_ICV_IGRPEN0_EL1_Type_Enable w__135)))
  else (pure (()))
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 7)) && (crm == 12)) : Bool)
  then
    (do
      let w__136 ← (( do readReg ICH_VMCR_EL2 ) : SailME Unit (BitVec 64) )
      let w__137 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailME Unit (BitVec 64) )
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__136 1 1
        (_get_ICV_IGRPEN1_EL1_Type_Enable w__137)))
  else (pure (()))


end ArmFull.Functions
