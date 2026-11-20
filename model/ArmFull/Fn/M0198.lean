module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0188
public import ArmFull.Fn.M0189 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_S1E0POEnabled (regime : Regime) (nv1 : (BitVec 1)) : SailM Bool := do
  ArmFull.assert (HasUnprivileged regime) "sail-inputs/03-v8_base.sail:24035.34-24035.35"
  let w__0 ← (( do (HaveS1POExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      match regime with
      | .Regime_EL20 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__2 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_E0POE w__2) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL10 =>
        (do
          if ((← do
               (pure ((← do
                     (IsTCR2EL1Enabled ())) && ((nv1 == 0#1) : Bool)))) : Bool)
          then
            (do
              let w__6 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL1_Type_E0POE w__6) == 1#1) : Bool))))
          else (pure false))
      | _ =>
        (do
          (undefined_bool_at (← occLabel 1420) ())))


def AArch64_S1POEnabled (regime : Regime) : SailM Bool := do
  let w__0 ← (( do (HaveS1POExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      match regime with
      | .Regime_EL3 =>
        (do
          let w__1 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
          (pure (((_get_TCR_EL3_Type_POE w__1) == 1#1))))
      | .Regime_EL2 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_POE w__3) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL20 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__6 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_POE w__6) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL10 =>
        (do
          if ((← do
               (IsTCR2EL1Enabled ())) : Bool)
          then
            (do
              let w__9 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL1_Type_POE w__9) == 1#1) : Bool))))
          else (pure false))
      | _ =>
        (do
          (undefined_bool_at (← occLabel 1453) ())))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_RLS2TTWParams (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (AArch64_NSS2TTWParams s1aarch64) ) : SailM S2TTWParams )
  let w__2 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__4 ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__3))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__4 } : S2TTWParams)
  (pure (walkparams))


def IsD128Enabled (el : (BitVec 2)) : SailM Bool := do
  let d128enabled ← (( do (undefined_bool_at (← occLabel 1657) ()) ) : SailM Bool )
  let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let questionMark := el
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__1 ← (( do (ELIsInHost EL0) ) : SailM Bool )
          if ((! w__1) : Bool)
          then
            (do
              if ((← do
                   (IsTCR2EL1Enabled ())) : Bool)
              then
                (do
                  let w__3 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL1_Type_D128 w__3) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((← do
                   (IsTCR2EL2Enabled ())) : Bool)
              then
                (do
                  let w__6 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL2_Type_D128 w__6) == 1#1) : Bool))))
              else (pure false)))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              if ((← do
                   (IsTCR2EL1Enabled ())) : Bool)
              then
                (do
                  let w__9 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL1_Type_D128 w__9) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  if ((← do
                       if ((← do
                            (IsTCR2EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HCR_EL2_Type_E2H w__12) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__14 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_TCR2_EL2_Type_D128 w__14) == 1#1) : Bool))))
                  else (pure false))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                      let d128enabled := (((_get_TCR_EL3_Type_D128 w__16) == 1#1) : Bool)
                      (pure (d128enabled)))
                  else (pure (d128enabled))))))
  else (pure (false))


def GCSPCREnabled (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       (GCSPCRSelected el)) : Bool)
  then
    (do
      (GCSEnabled el))
  else (pure false)


def CheckMOPSEnabled (_ : Unit) : SailM Unit := do
  let w__12 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   if ((← do
                        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__0.EL == EL0) : Bool)))) : Bool)
                   then (pure true)
                   else
                     (do
                       let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__1.EL == EL1) : Bool))))) : Bool)
              then
                (do
                  (EL2Enabled ()))
              else (pure false)) : Bool)
         then
           (do
             if ((← do
                  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_E2H w__6) == 0#1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__9 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
             (pure (((! w__9) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__10 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCRX_EL2_Type_MSCEn w__10) == 0#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__12 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__21 ← (( do
    if ((← do
         if ((← do
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__13.EL == EL0) : Bool)))) : Bool)
         then
           (do
             let w__14 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
             (pure ((((_get_SCTLR_EL1_Type_MSCEn w__14) == 0#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__16 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  (pure (((! w__16) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_TGE w__17) == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__19) == 0#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__21 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__26 ← (( do
    if ((← do
         if ((← do
              let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__22.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (IsInHost ()))
         else (pure false)) : Bool)
    then
      (do
        let w__25 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLR_EL2_Type_MSCEn w__25) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__26 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))


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
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            (pure (((w__2 == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let w__7 ← (( do
    if ((← do
         if (((! route_to_el3) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__6.EL == EL1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__7 : Bool)
    then
      (do
        let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let route_to_el2 := (((_get_HCR_EL2_Type_AMO w__8) == 1#1) : Bool)
        (pure (route_to_el2)))
    else
      (do
        let w__12 ← (( do
          if ((← do
               if (((! route_to_el3) : Bool) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__11.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__12 : Bool)
        then
          (do
            if ((← do
                 let w__13 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__13) : Bool)))) : Bool)
            then
              (do
                let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_TGE w__14) +++ (_get_HCR_EL2_Type_AMO w__15)) != 0b00#2) : Bool))))
            else (pure false))
        else (pure (false))) ) : SailM Bool )
  let masked ← (( do (undefined_bool_at (← occLabel 1922) ()) ) : SailM Bool )
  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__17.EL
  let masked ← (( do
    if ((questionMark == EL3) : Bool)
    then
      (do
        if ((← do
             let w__18 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
             (pure (((w__18 == 0#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__19.A == 1#1) : Bool)))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            if (((! route_to_el3) : Bool) : Bool)
            then
              (do
                if ((← do
                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_TGE w__21) +++ (_get_HCR_EL2_Type_AMO w__22)) == 0b00#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__23.A == 1#1) : Bool)))))
            else (pure false))
        else
          (do
            if ((questionMark == EL1) : Bool)
            then
              (do
                if ((((! route_to_el3) && (! route_to_el2)) : Bool) : Bool)
                then
                  (do
                    let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__26.A == 1#1) : Bool))))
                else (pure false))
            else
              (do
                if ((questionMark == EL0) : Bool)
                then
                  (do
                    if ((((! route_to_el3) && (! route_to_el2)) : Bool) : Bool)
                    then
                      (do
                        let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__28.A == 1#1) : Bool))))
                    else (pure false))
                else (pure (masked))))) ) : SailM Bool )
  let w__30 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let masked ← (( do
    if (w__30 : Bool)
    then
      (do
        let nmea_bit ← (( do (undefined_bitvector_at (← occLabel 1923) 1) ) : SailM (BitVec 1) )
        let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
        let questionMark := w__31.EL
        let nmea_bit ← (( do
          if ((questionMark == EL3) : Bool)
          then
            (do
              let w__32 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              let nmea_bit := ((_get_SCR_EL3_Type_NMEA w__32) : (BitVec 1))
              (pure (nmea_bit)))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__33 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      let w__34 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_SCTLR2_EL2_Type_NMEA w__34))))
                  else (pure (0#1)))
              else
                (do
                  if ((questionMark == EL1) : Bool)
                  then
                    (do
                      let w__36 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                          (pure ((_get_SCTLR2_EL1_Type_NMEA w__37))))
                      else (pure (0#1)))
                  else
                    (do
                      if ((questionMark == EL0) : Bool)
                      then
                        (do
                          let w__39 ← (( do (IsInHost ()) ) : SailM Bool )
                          if (w__39 : Bool)
                          then
                            (do
                              let w__40 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                              if (w__40 : Bool)
                              then
                                (do
                                  let w__41 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                                  (pure ((_get_SCTLR2_EL2_Type_NMEA w__41))))
                              else (pure (0#1)))
                          else
                            (do
                              let w__43 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                              if (w__43 : Bool)
                              then
                                (do
                                  let w__44 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                                  (pure ((_get_SCTLR2_EL1_Type_NMEA w__44))))
                              else (pure (0#1))))
                      else (pure (nmea_bit))))) ) : SailM (BitVec 1) )
        let masked : Bool := (masked && (nmea_bit == 0#1))
        (pure (masked)))
    else
      (do
        let w__48 ← (( do
          if ((← do
               (HaveDoubleFaultExt ())) : Bool)
          then
            (do
              let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__47.EL == EL3) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__48 : Bool)
        then
          (do
            let w__49 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__50 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            let nmea_bit : (BitVec 1) := ((_get_SCR_EL3_Type_NMEA w__49) &&& w__50)
            let masked : Bool := (masked && (nmea_bit == 0#1))
            (pure (masked)))
        else (pure (masked))) ) : SailM Bool )
  let route_masked_to_el3 ← (( do (undefined_bool_at (← occLabel 1924) ()) ) : SailM Bool )
  let route_masked_to_el2 ← (( do (undefined_bool_at (← occLabel 1925) ()) ) : SailM Bool )
  let w__51 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let (route_masked_to_el2, route_masked_to_el3) ← (( do
    if (w__51 : Bool)
    then
      (do
        let w__67 ← (( do
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
                   let w__56 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCRX_EL2_Type_TMEA w__56) == 1#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__58 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__58.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (pure ((← do
                             let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__59.A == 1#1) : Bool)))) || (masked : Bool))))
                   else (pure false)) : Bool)
              then (pure true)
              else
                (do
                  if ((← do
                       (pure ((← do
                             let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__62.EL == EL0) : Bool)))) && (masked : Bool)))) : Bool)
                  then
                    (do
                      let w__64 ← (( do (IsInHost ()) ) : SailM Bool )
                      (pure (((! w__64) : Bool))))
                  else (pure false)))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el2 := (w__67 : Bool)
        let w__81 ← (( do
          if ((← do
               (pure ((← do
                     if ((← do
                          (HaveEL EL3)) : Bool)
                     then
                       (do
                         let w__69 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_TMEA w__69) == 1#1) : Bool))))
                     else (pure false)) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        if ((← do
                             let w__72 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__72.EL == EL2) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__73.EL == EL1) : Bool))))) : Bool)
                   then
                     (do
                       (pure ((← do
                             let w__75 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__75.A == 1#1) : Bool)))) || (masked : Bool))))
                   else (pure false)) : Bool)
              then (pure true)
              else
                (do
                  (pure ((← do
                        let w__78 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__78.EL == EL0) : Bool)))) && (masked : Bool)))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el3 := (w__81 : Bool)
        (pure ((route_masked_to_el2, route_masked_to_el3))))
    else
      (let route_masked_to_el2 : Bool := false
      let route_masked_to_el3 : Bool := false
      (pure ((route_masked_to_el2, route_masked_to_el3)))) ) : SailM (Bool × Bool) )
  let take_in_el3 ← (( do
    (pure ((← do
          let w__82 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__82.EL == EL3) : Bool)))) && ((! masked) : Bool))) ) : SailM Bool )
  let take_in_el2_0 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     let w__83 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((w__83.EL == EL2) : Bool)))) : Bool)
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
                           let w__87 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__87.EL == EL1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          if ((← do
                               let w__88 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__88.EL == EL0) : Bool)))) : Bool)
                          then
                            (do
                              let w__89 ← (( do (IsInHost ()) ) : SailM Bool )
                              (pure (((! w__89) : Bool))))
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
              let w__94 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
              let target_el := (w__94 : (BitVec 2))
              (pure ((masked, target_el))))))


end ArmFull.Functions
