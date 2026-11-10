import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0087
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0173
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187

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

/-- Type quantifiers: k_implicit_esb : Bool -/
def AArch64_PhysicalSErrorSyndrome (implicit_esb : Bool) : SailM (BitVec 25) := do
  let syndrome : (BitVec 25) := (Zeros (n := 25))
  let fault ← (( do (GetPendingPhysicalSError ()) ) : SailM FaultRecord )
  let errorstate ← (( do (AArch64_PEErrorState fault) ) : SailM ErrorState )
  if ((BEq.beq errorstate ErrorState_Uncategorized) : Bool)
  then
    (let syndrome : (BitVec 25) := (Zeros (n := 25))
    (pure (syndrome)))
  else
    (do
      if ((BEq.beq errorstate ErrorState_IMPDEF) : Bool)
      then
        (do
          let syndrome : (BitVec 25) := (BitVec.update syndrome 24 (Bit 1#1))
          let w__0 ← (( do (__IMPDEF_bits 24 "IMPDEF ErrorState") ) : SailM (BitVec 24) )
          let syndrome := ((Sail.BitVec.updateSubrange syndrome 23 0 w__0) : (BitVec 25))
          (pure (syndrome)))
      else
        (do
          let syndrome : (BitVec 25) := (BitVec.update syndrome 24 (Bit 0#1))
          let syndrome : (BitVec 25) :=
            (BitVec.update syndrome 13
              (Bit
                (if (implicit_esb : Bool)
                then 1#1
                else 0#1)))
          let w__1 ← (( do (AArch64_EncodeAsyncErrorSyndrome errorstate) ) : SailM (BitVec 3) )
          let syndrome := ((Sail.BitVec.updateSubrange syndrome 12 10 w__1) : (BitVec 25))
          let syndrome : (BitVec 25) := (BitVec.update syndrome 9 (Bit fault.extflag))
          let syndrome : (BitVec 25) := (Sail.BitVec.updateSubrange syndrome 5 0 0b010001#6)
          (pure (syndrome))))


def AArch64_PhysicalSErrorTarget (_ : Unit) : SailM (Bool × (BitVec 2)) := do
  let route_to_el3 ← (( do (undefined_bool_at (← occLabel 1920) ()) ) : SailM Bool )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 1921) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let route_to_el3 ← (( do
    if ((w__0.EL != EL3) : Bool)
    then
      (do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            (pure (((w__1 == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let w__6 ← (( do
    if ((← do
         if (((! route_to_el3) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__5.EL == EL1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let route_to_el2 := (((_get_HCR_EL2_Type_AMO w__7) == 1#1) : Bool)
        (pure (route_to_el2)))
    else
      (do
        let w__11 ← (( do
          if ((← do
               if (((! route_to_el3) : Bool) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__10.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__11 : Bool)
        then
          (do
            if ((← do
                 let w__12 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__12) : Bool)))) : Bool)
            then
              (do
                let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_TGE w__13) +++ (_get_HCR_EL2_Type_AMO w__14)) != 0b00#2) : Bool))))
            else (pure false))
        else (pure (false))) ) : SailM Bool )
  let masked ← (( do (undefined_bool_at (← occLabel 1922) ()) ) : SailM Bool )
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__16.EL
  let masked ← (( do
    if ((questionMark == EL3) : Bool)
    then
      (do
        if ((← do
             let w__17 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
             (pure (((w__17 == 0#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__18.A == 1#1) : Bool)))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            if (((! route_to_el3) : Bool) : Bool)
            then
              (do
                if ((← do
                     let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_TGE w__20) +++ (_get_HCR_EL2_Type_AMO w__21)) == 0b00#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__22.A == 1#1) : Bool)))))
            else (pure false))
        else
          (do
            if ((questionMark == EL1) : Bool)
            then
              (do
                if ((((! route_to_el3) && (! route_to_el2)) : Bool) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__25.A == 1#1) : Bool))))
                else (pure false))
            else
              (do
                if ((questionMark == EL0) : Bool)
                then
                  (do
                    if ((((! route_to_el3) && (! route_to_el2)) : Bool) : Bool)
                    then
                      (do
                        let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__27.A == 1#1) : Bool))))
                    else (pure false))
                else (pure (masked))))) ) : SailM Bool )
  let w__29 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let masked ← (( do
    if (w__29 : Bool)
    then
      (do
        let nmea_bit ← (( do (undefined_bitvector_at (← occLabel 1923) 1) ) : SailM (BitVec 1) )
        let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
        let questionMark := w__30.EL
        let nmea_bit ← (( do
          if ((questionMark == EL3) : Bool)
          then
            (do
              let w__31 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              let nmea_bit := ((_get_SCR_EL3_Type_NMEA w__31) : (BitVec 1))
              (pure (nmea_bit)))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__32 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__33 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_SCTLR2_EL2_Type_NMEA w__33))))
                  else (pure (0#1)))
              else
                (do
                  if ((questionMark == EL1) : Bool)
                  then
                    (do
                      let w__35 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                      if (w__35 : Bool)
                      then
                        (do
                          let w__36 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                          (pure ((_get_SCTLR2_EL1_Type_NMEA w__36))))
                      else (pure (0#1)))
                  else
                    (do
                      if ((questionMark == EL0) : Bool)
                      then
                        (do
                          let w__38 ← (( do (IsInHost ()) ) : SailM Bool )
                          if (w__38 : Bool)
                          then
                            (do
                              let w__39 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  let w__40 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                                  (pure ((_get_SCTLR2_EL2_Type_NMEA w__40))))
                              else (pure (0#1)))
                          else
                            (do
                              let w__42 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                              if (w__42 : Bool)
                              then
                                (do
                                  let w__43 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                                  (pure ((_get_SCTLR2_EL1_Type_NMEA w__43))))
                              else (pure (0#1))))
                      else (pure (nmea_bit))))) ) : SailM (BitVec 1) )
        let masked : Bool := (masked && (nmea_bit == 0#1))
        (pure (masked)))
    else
      (do
        let w__47 ← (( do
          if ((← do
               (HaveDoubleFaultExt ())) : Bool)
          then
            (do
              let w__46 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__46.EL == EL3) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__47 : Bool)
        then
          (do
            let w__48 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__49 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            let nmea_bit : (BitVec 1) := ((_get_SCR_EL3_Type_NMEA w__48) &&& w__49)
            let masked : Bool := (masked && (nmea_bit == 0#1))
            (pure (masked)))
        else (pure (masked))) ) : SailM Bool )
  let route_masked_to_el3 ← (( do (undefined_bool_at (← occLabel 1924) ()) ) : SailM Bool )
  let route_masked_to_el2 ← (( do (undefined_bool_at (← occLabel 1925) ()) ) : SailM Bool )
  let w__50 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let (route_masked_to_el2, route_masked_to_el3) ← (( do
    if (w__50 : Bool)
    then
      (do
        let w__66 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         (pure ((← do
                               (EL2Enabled ())) && ((! route_to_el3) : Bool)))) : Bool)
                    then
                      (do
                        (IsHCRXEL2Enabled ()))
                    else (pure false)) : Bool)
               then
                 (do
                   let w__55 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCRX_EL2_Type_TMEA w__55) == 1#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__57 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__57.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (pure ((← do
                             let w__58 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__58.A == 1#1) : Bool)))) || (masked : Bool))))
                   else (pure false)) : Bool)
              then (pure true)
              else
                (do
                  if ((← do
                       (pure ((← do
                             let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__61.EL == EL0) : Bool)))) && (masked : Bool)))) : Bool)
                  then
                    (do
                      let w__63 ← (( do (IsInHost ()) ) : SailM Bool )
                      (pure (((! w__63) : Bool))))
                  else (pure false)))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el2 := (w__66 : Bool)
        let w__79 ← (( do
          if ((← do
               (pure ((← do
                     if (((HaveEL EL3) : Bool) : Bool)
                     then
                       (do
                         let w__67 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_TMEA w__67) == 1#1) : Bool))))
                     else (pure false)) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        if ((← do
                             let w__70 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__70.EL == EL2) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__71 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__71.EL == EL1) : Bool))))) : Bool)
                   then
                     (do
                       (pure ((← do
                             let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__73.A == 1#1) : Bool)))) || (masked : Bool))))
                   else (pure false)) : Bool)
              then (pure true)
              else
                (do
                  (pure ((← do
                        let w__76 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__76.EL == EL0) : Bool)))) && (masked : Bool)))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el3 := (w__79 : Bool)
        (pure ((route_masked_to_el2, route_masked_to_el3))))
    else
      (let route_masked_to_el2 : Bool := false
      let route_masked_to_el3 : Bool := false
      (pure ((route_masked_to_el2, route_masked_to_el3)))) ) : SailM (Bool × Bool) )
  let take_in_el3 ← (( do
    (pure ((← do
          let w__80 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__80.EL == EL3) : Bool)))) && ((! masked) : Bool))) ) : SailM Bool )
  let take_in_el2_0 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     let w__81 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((w__81.EL == EL2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (IsInHost ()))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool)))) && ((! masked) : Bool)))
    ) : SailM Bool )
  let take_in_el1_0 ← (( do
    (pure ((← do
          (pure ((← do
                (pure ((← do
                      if ((← do
                           let w__85 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__85.EL == EL1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          if ((← do
                               let w__86 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__86.EL == EL0) : Bool)))) : Bool)
                          then
                            (do
                              let w__87 ← (( do (IsInHost ()) ) : SailM Bool )
                              (pure (((! w__87) : Bool))))
                          else (pure false))) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool)))) && ((! masked) : Bool)))
    ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 1926) 2) ) : SailM (BitVec 2) )
  if (((take_in_el3 || route_to_el3) || route_masked_to_el3) : Bool)
  then
    (let masked : Bool := false
    let target_el : (BitVec 2) := EL3
    (pure ((masked, target_el))))
  else
    (do
      if (((take_in_el2_0 || route_to_el2) || route_masked_to_el2) : Bool)
      then
        (let masked : Bool := false
        let target_el : (BitVec 2) := EL2
        (pure ((masked, target_el))))
      else
        (do
          if (take_in_el1_0 : Bool)
          then
            (let masked : Bool := false
            let target_el : (BitVec 2) := EL1
            (pure ((masked, target_el))))
          else
            (do
              let masked : Bool := true
              let w__92 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
              let target_el := (w__92 : (BitVec 2))
              (pure ((masked, target_el))))))


def CSSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CSSELR_Type (← occLabel 2128) ()) ) : SailM CSSELR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CSSELR_S)
  else
    (do
      (CSSELR_NS_read ()))


def CSSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CSSELR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg CSSELR_S r)
  else
    (do
      (CSSELR_NS_write r))


def DFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_DFSR_Type (← occLabel 2142) ()) ) : SailM DFSR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg DFSR_S)
  else
    (do
      (DFSR_NS_read ()))


def ICC_BPR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_BPR1_Type (← occLabel 2160) ()) ) : SailM ICC_BPR1_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_BPR1_S_read ()))
  else
    (do
      (ICC_BPR1_NS_read ()))


def ICC_BPR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_BPR1_S_write r))
  else
    (do
      (ICC_BPR1_NS_write r))


def ICC_CTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_CTLR_Type (← occLabel 2163) ()) ) : SailM ICC_CTLR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_CTLR_S_read ()))
  else
    (do
      (ICC_CTLR_NS_read ()))


def ICC_CTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_CTLR_S_write r))
  else
    (do
      (ICC_CTLR_NS_write r))


def ICC_IGRPEN1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_IGRPEN1_Type (← occLabel 2184) ()) ) : SailM ICC_IGRPEN1_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_IGRPEN1_S_read ()))
  else
    (do
      (ICC_IGRPEN1_NS_read ()))


def ICC_IGRPEN1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_IGRPEN1_S_write r))
  else
    (do
      (ICC_IGRPEN1_NS_write r))


def ICC_SRE_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_SRE_Type (← occLabel 2194) ()) ) : SailM ICC_SRE_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_SRE_S_read ()))
  else
    (do
      (ICC_SRE_NS_read ()))


def ICC_SRE_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (ICC_SRE_S_write r))
  else
    (do
      (ICC_SRE_NS_write r))


def IFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_IFSR_Type (← occLabel 2245) ()) ) : SailM IFSR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg IFSR_S)
  else
    (do
      (IFSR_NS_read ()))


end ArmFull.Functions
