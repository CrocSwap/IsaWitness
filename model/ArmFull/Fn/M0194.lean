module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0187 set_option backward.proofsInPublic true @[expose] public section

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

def BranchRecordAllowed (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (ELUsingAArch32 el) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      if (((_get_BRBFCR_EL1_Type_PAUSED w__1) == 1#1) : Bool)
      then (pure (false))
      else
        (do
          let w__3 ← (( do
            if (((el == EL3) : Bool) : Bool)
            then
              (do
                (HaveBRBEv1p1 ()))
            else (pure false) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let w__5 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_MDCR_EL3_Type_E3BREC w__4) != (_get_MDCR_EL3_Type_E3BREW w__5)))))
          else
            (do
              let w__12 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    if ((← do
                         let w__7 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_SBRBE w__7) == 0b00#2) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((← do
                             let w__8 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                             (pure (((BEq.beq w__8 SS_Secure) : Bool)))) : Bool)
                        then
                          (do
                            let w__9 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_MDCR_EL3_Type_SBRBE w__9) == 0b01#2) : Bool))))
                        else (pure false)))
                else (pure false) ) : SailM Bool )
              if (w__12 : Bool)
              then (pure (false))
              else
                (do
                  let questionMark := el
                  if ((questionMark == EL3) : Bool)
                  then (pure (false))
                  else
                    (do
                      if ((questionMark == EL2) : Bool)
                      then
                        (do
                          let w__13 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((_get_BRBCR_EL2_Type_E2BRE w__13) == 1#1))))
                      else
                        (do
                          if ((questionMark == EL1) : Bool)
                          then
                            (do
                              let w__14 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
                              (pure (((_get_BRBCR_EL1_Type_E1BRE w__14) == 1#1))))
                          else
                            (do
                              if ((questionMark == EL0) : Bool)
                              then
                                (do
                                  let w__17 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      let w__18 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((_get_BRBCR_EL2_Type_E0HBRE w__18) == 1#1))))
                                  else
                                    (do
                                      let w__19 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
                                      (pure (((_get_BRBCR_EL1_Type_E0BRE w__19) == 1#1)))))
                              else
                                (do
                                  (undefined_bool_at (← occLabel 562) ())))))))))


def S1TranslationRegime__1 (_ : Unit) : SailM (BitVec 2) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (S1TranslationRegime w__0.EL)


/-- Type quantifiers: k_IsInstr : Bool -/
def EffectiveTBI (address : (BitVec 64)) (IsInstr : Bool) (el : (BitVec 2)) : SailM (BitVec 1) := do
  let tbi ← (( do (undefined_bitvector_at (← occLabel 567) 1) ) : SailM (BitVec 1) )
  let tbid ← (( do (undefined_bitvector_at (← occLabel 568) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do (HaveEL el) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:6080.21-6080.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:6082.43-6082.44"
  let questionMark := regime
  let (tbi, tbid) ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        let w__4 ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
          then
            (do
              let w__2 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBI1 w__2))))
          else
            (do
              let w__3 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBI0 w__3)))) ) : SailM (BitVec 1) )
        let tbi := (w__4 : (BitVec 1))
        let w__5 ← (( do (HavePACExt ()) ) : SailM Bool )
        let tbid ← (( do
          if (w__5 : Bool)
          then
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
              then
                (do
                  let w__6 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL1_Type_TBID1 w__6))))
              else
                (do
                  let w__7 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL1_Type_TBID0 w__7)))))
          else (pure (tbid)) ) : SailM (BitVec 1) )
        (pure ((tbi, tbid))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            let w__11 ← (( do
              if ((← do
                   (HaveVirtHostExt ())) : Bool)
              then
                (do
                  (ELIsInHost el))
              else (pure false) ) : SailM Bool )
            if (w__11 : Bool)
            then
              (do
                let w__14 ← (( do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                  then
                    (do
                      let w__12 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_TBI1 w__12))))
                  else
                    (do
                      let w__13 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_TBI0 w__13)))) ) : SailM (BitVec 1) )
                let tbi := (w__14 : (BitVec 1))
                let w__15 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__15 : Bool)
                  then
                    (do
                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                      then
                        (do
                          let w__16 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((_get_TCR_EL2_Type_TBID1 w__16))))
                      else
                        (do
                          let w__17 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((_get_TCR_EL2_Type_TBID0 w__17)))))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid))))
            else
              (do
                let w__19 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                let tbi := ((_get_TCR_EL2_Type_TBI w__19) : (BitVec 1))
                let w__20 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__20 : Bool)
                  then
                    (do
                      let w__21 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      let tbid := ((_get_TCR_EL2_Type_TBID w__21) : (BitVec 1))
                      (pure (tbid)))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid)))))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                let w__22 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                let tbi := ((_get_TCR_EL3_Type_TBI w__22) : (BitVec 1))
                let w__23 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__23 : Bool)
                  then
                    (do
                      let w__24 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                      let tbid := ((_get_TCR_EL3_Type_TBID w__24) : (BitVec 1))
                      (pure (tbid)))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid))))
            else (pure ((tbi, tbid))))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let w__28 ← (( do
    if (((tbi == 1#1) : Bool) : Bool)
    then
      (do
        (pure ((← do
              (pure ((← do
                    let w__25 ← (( do (HavePACExt ()) ) : SailM Bool )
                    (pure (((! w__25) : Bool)))) || ((tbid == 0#1) : Bool)))) || ((! IsInstr) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__29 : (BitVec 1) :=
    if (w__28 : Bool)
    then 1#1
    else 0#1
  (pure (w__29))


/-- Type quantifiers: n : Int -/
def Rmode_read (n : Int) (mode : (BitVec 5)) : SailM (BitVec 32) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 14)) "sail-inputs/03-v8_base.sail:6376.27-6376.28"
  let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  if ((bne w__0 SS_Secure) : Bool)
  then
    (do
      ArmFull.assert (mode != M32_Monitor) "sail-inputs/03-v8_base.sail:6378.34-6378.35")
  else (pure (()))
  let w__1 ← (( do (BadMode mode) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:6380.34-6380.35"
  if ((mode == M32_Monitor) : Bool)
  then
    (do
      if ((n == 13) : Bool)
      then
        (do
          readReg SP_mon)
      else
        (do
          if ((n == 14) : Bool)
          then
            (do
              readReg LR_mon)
          else
            (do
              let w__4 ← (( do (get_R (Sail.Int.toNatChecked (n))) ) : SailM (BitVec 64) )
              (pure ((Sail.BitVec.extractLsb w__4 31 0))))))
  else
    (do
      let w__7 ← (( do (LookUpRIndex (Sail.Int.toNatChecked (n)) mode) ) : SailM Int )
      let w__8 ← (( do (get_R (Sail.Int.toNatChecked (w__7))) ) : SailM (BitVec 64) )
      (pure ((Sail.BitVec.extractLsb w__8 31 0))))


def StatisticalProfilingEnabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (StatisticalProfilingEnabled__1 w__0.EL)


def CurrentNSVL_read (_ : Unit) : SailM Int := do
  let vl ← (( do (undefined_int_at (← occLabel 602) ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool)))) : Bool)
        then
          (do
            let w__2 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false)) ) : SailM Bool )
  let vl ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_ZCR_EL1_Type_LEN w__5)) : Int)
        (pure (vl)))
    else (pure (vl)) ) : SailM Int )
  let w__10 ← (( do
    if ((← do
         let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__6.EL == EL2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__7.EL == EL0) : Bool)))) : Bool)
        then
          (do
            (IsInHost ()))
        else (pure false)) ) : SailM Bool )
  let vl ← (( do
    if (w__10 : Bool)
    then
      (do
        let w__11 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_ZCR_EL2_Type_LEN w__11)) : Int)
        (pure (vl)))
    else
      (do
        let w__16 ← (( do
          if ((← do
               if ((← do
                    let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__12.EL == EL0) : Bool)))) : Bool)
               then (pure true)
               else
                 (do
                   let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__13.EL == EL1) : Bool))))) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        if (w__16 : Bool)
        then
          (do
            let w__17 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_ZCR_EL2_Type_LEN w__17))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
  let vl ← (( do
    if ((w__18.EL == EL3) : Bool)
    then
      (do
        let w__19 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_ZCR_EL3_Type_LEN w__19)) : Int)
        (pure (vl)))
    else
      (do
        let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
        if (w__20 : Bool)
        then
          (do
            let w__21 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_ZCR_EL3_Type_LEN w__21))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let vl : Int := ((vl +i 1) *i 128)
  let vl ← (( do (ImplementedSVEVectorLength vl) ) : SailM Int )
  (__ArmCertRequireVectorLength vl)


def CurrentSVL_read (_ : Unit) : SailM Int := do
  let vl ← (( do (undefined_int_at (← occLabel 606) ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool)))) : Bool)
        then
          (do
            let w__2 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false)) ) : SailM Bool )
  let vl ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_SMCR_EL1_Type_LEN w__5)) : Int)
        (pure (vl)))
    else (pure (vl)) ) : SailM Int )
  let w__10 ← (( do
    if ((← do
         let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__6.EL == EL2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__7.EL == EL0) : Bool)))) : Bool)
        then
          (do
            (IsInHost ()))
        else (pure false)) ) : SailM Bool )
  let vl ← (( do
    if (w__10 : Bool)
    then
      (do
        let w__11 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_SMCR_EL2_Type_LEN w__11)) : Int)
        (pure (vl)))
    else
      (do
        let w__16 ← (( do
          if ((← do
               if ((← do
                    let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__12.EL == EL0) : Bool)))) : Bool)
               then (pure true)
               else
                 (do
                   let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__13.EL == EL1) : Bool))))) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        if (w__16 : Bool)
        then
          (do
            let w__17 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_SMCR_EL2_Type_LEN w__17))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
  let vl ← (( do
    if ((w__18.EL == EL3) : Bool)
    then
      (do
        let w__19 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
        let vl : Int := ((BitVec.toNat (_get_SMCR_EL3_Type_LEN w__19)) : Int)
        (pure (vl)))
    else
      (do
        let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
        if (w__20 : Bool)
        then
          (do
            let w__21 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_SMCR_EL3_Type_LEN w__21))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let vl : Int := ((vl +i 1) *i 128)
  let vl ← (( do (ImplementedSMEVectorLength vl) ) : SailM Int )
  (__ArmCertRequireVectorLength vl)


def AArch64_IsFPEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  let w__1 ← (( do
    if ((((el == EL0) || (el == EL1)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (IsInHost ()) ) : SailME Bool Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailME Bool Bool )
  if (w__1 : Bool)
  then
    (do
      let disabled ← (( do (undefined_bool_at (← occLabel 614) ()) ) : SailME Bool Bool )
      let w__2 ← (( do readReg CPACR_EL1 ) : SailME Bool (BitVec 64) )
      let b__0 := (_get_CPACR_EL1_Type_FPEN w__2)
      let disabled : Bool :=
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
        then true
        else
          (match b__0 with
          | 0b01 => (el == EL0)
          | _ => false)
      let disabled := disabled
      if (disabled : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  let w__4 ← (( do
    if ((((el == EL0) || ((el == EL1) || (el == EL2))) : Bool) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailME Bool Bool )
  if (w__4 : Bool)
  then
    (do
      let w__7 ← (( do
        if ((← do
             (HaveVirtHostExt ())) : Bool)
        then
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__6) == 1#1) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__7 : Bool)
      then
        (do
          let disabled ← (( do (undefined_bool_at (← occLabel 615) ()) ) : SailME Bool Bool )
          let w__8 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
          let b__1 := (_get_CPTR_EL2_Type_FPEN w__8)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__1 with
                | 0b01 =>
                  (do
                    if (((el == EL0) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__9) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailME Bool Bool )
          let disabled := disabled
          if (disabled : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else
        (do
          let w__11 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TFP w__11) == 1#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (()))))
  else (pure (()))
  let w__12 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
  if (w__12 : Bool)
  then
    (do
      let w__13 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
      if (((_get_CPTR_EL3_Type_TFP w__13) == 1#1) : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  (pure (true))


def IsOriginalSVEEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  let disabled ← (( do (undefined_bool_at (← occLabel 620) ()) ) : SailME Bool Bool )
  let w__0 ← (( do (ELUsingAArch32 el) ) : SailME Bool Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if ((((el == EL0) || (el == EL1)) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (IsInHost ()) ) : SailME Bool Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      let disabled ← (( do
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg CPACR_EL1 ) : SailME Bool (BitVec 64) )
            let b__0 := (_get_CPACR_EL1_Type_ZEN w__3)
            let disabled : Bool :=
              if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
              then true
              else
                (match b__0 with
                | 0b01 => (el == EL0)
                | _ => false)
            if (disabled : Bool)
            then
              (do
                SailME.throw (false : Bool))
            else (pure (()))
            (pure (disabled)))
        else (pure (disabled)) ) : SailME Bool Bool )
      let w__5 ← (( do
        if ((((el == EL0) || ((el == EL1) || (el == EL2))) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__5 : Bool)
      then
        (do
          let w__8 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_E2H w__7) == 1#1) : Bool))))
            else (pure false) ) : SailME Bool Bool )
          if (w__8 : Bool)
          then
            (do
              let w__9 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
              let b__1 := (_get_CPTR_EL2_Type_ZEN w__9)
              let disabled ← (( do
                if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                then (pure (true))
                else
                  (do
                    match b__1 with
                    | 0b01 =>
                      (do
                        if (((el == EL0) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__10) == 1#1) : Bool))))
                        else (pure false))
                    | _ => (pure (false))) ) : SailME Bool Bool )
              if (disabled : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (())))
          else
            (do
              let w__12 ← (( do readReg CPTR_EL2 ) : SailME Bool (BitVec 64) )
              if (((_get_CPTR_EL2_Type_TZ w__12) == 1#1) : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (()))))
      else (pure (()))
      let w__13 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_EZ w__14) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


end ArmFull.Functions
