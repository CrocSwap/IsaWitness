import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0039
import ArmFull.Fn.M0041
import ArmFull.Fn.M0097
import ArmFull.Fn.M0144
import ArmFull.Fn.M0153
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186

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

def S1TranslationRegime__1 (_ : Unit) : SailM (BitVec 2) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (S1TranslationRegime w__0.EL)


/-- Type quantifiers: k_IsInstr : Bool -/
def EffectiveTBI (address : (BitVec 64)) (IsInstr : Bool) (el : (BitVec 2)) : SailM (BitVec 1) := do
  let tbi ← (( do (undefined_bitvector_at (← occLabel 567) 1) ) : SailM (BitVec 1) )
  let tbid ← (( do (undefined_bitvector_at (← occLabel 568) 1) ) : SailM (BitVec 1) )
  ArmFull.assert (HaveEL el) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6080.21-6080.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6082.43-6082.44"
  let questionMark := regime
  let (tbi, tbid) ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        let w__3 ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
          then
            (do
              let w__1 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBI1 w__1))))
          else
            (do
              let w__2 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBI0 w__2)))) ) : SailM (BitVec 1) )
        let tbi := (w__3 : (BitVec 1))
        let w__4 ← (( do (HavePACExt ()) ) : SailM Bool )
        let tbid ← (( do
          if (w__4 : Bool)
          then
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL1_Type_TBID1 w__5))))
              else
                (do
                  let w__6 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((_get_TCR_EL1_Type_TBID0 w__6)))))
          else (pure (tbid)) ) : SailM (BitVec 1) )
        (pure ((tbi, tbid))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            let w__10 ← (( do
              if ((← do
                   (HaveVirtHostExt ())) : Bool)
              then
                (do
                  (ELIsInHost el))
              else (pure false) ) : SailM Bool )
            if (w__10 : Bool)
            then
              (do
                let w__13 ← (( do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                  then
                    (do
                      let w__11 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_TBI1 w__11))))
                  else
                    (do
                      let w__12 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_TBI0 w__12)))) ) : SailM (BitVec 1) )
                let tbi := (w__13 : (BitVec 1))
                let w__14 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__14 : Bool)
                  then
                    (do
                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                      then
                        (do
                          let w__15 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((_get_TCR_EL2_Type_TBID1 w__15))))
                      else
                        (do
                          let w__16 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((_get_TCR_EL2_Type_TBID0 w__16)))))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid))))
            else
              (do
                let w__18 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                let tbi := ((_get_TCR_EL2_Type_TBI w__18) : (BitVec 1))
                let w__19 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__19 : Bool)
                  then
                    (do
                      let w__20 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      let tbid := ((_get_TCR_EL2_Type_TBID w__20) : (BitVec 1))
                      (pure (tbid)))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid)))))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                let w__21 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                let tbi := ((_get_TCR_EL3_Type_TBI w__21) : (BitVec 1))
                let w__22 ← (( do (HavePACExt ()) ) : SailM Bool )
                let tbid ← (( do
                  if (w__22 : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                      let tbid := ((_get_TCR_EL3_Type_TBID w__23) : (BitVec 1))
                      (pure (tbid)))
                  else (pure (tbid)) ) : SailM (BitVec 1) )
                (pure ((tbi, tbid))))
            else (pure ((tbi, tbid))))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let w__27 ← (( do
    if (((tbi == 1#1) : Bool) : Bool)
    then
      (do
        (pure ((← do
              (pure ((← do
                    let w__24 ← (( do (HavePACExt ()) ) : SailM Bool )
                    (pure (((! w__24) : Bool)))) || ((tbid == 0#1) : Bool)))) || ((! IsInstr) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__28 : (BitVec 1) :=
    if (w__27 : Bool)
    then 1#1
    else 0#1
  (pure (w__28))


/-- Type quantifiers: n : Int -/
def Rmode_read (n : Int) (mode : (BitVec 5)) : SailM (BitVec 32) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 14)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6376.27-6376.28"
  let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  if ((bne w__0 SS_Secure) : Bool)
  then
    (do
      ArmFull.assert (mode != M32_Monitor) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6378.34-6378.35")
  else (pure (()))
  let w__1 ← (( do (BadMode mode) ) : SailM Bool )
  ArmFull.assert (! w__1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6380.34-6380.35"
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
        if ((HaveEL EL3) : Bool)
        then
          (do
            let w__20 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_ZCR_EL3_Type_LEN w__20))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let vl : Int := ((vl +i 1) *i 128)
  let vl ← (( do (ImplementedSVEVectorLength vl) ) : SailM Int )
  (pure (vl))


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
        if ((HaveEL EL3) : Bool)
        then
          (do
            let w__20 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
            let vl : Int := ((Min.min vl (BitVec.toNat (_get_SMCR_EL3_Type_LEN w__20))) : Int)
            (pure (vl)))
        else (pure (vl))) ) : SailM Int )
  let vl : Int := ((vl +i 1) *i 128)
  let vl ← (( do (ImplementedSMEVectorLength vl) ) : SailM Int )
  (pure (vl))


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
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__12 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
      if (((_get_CPTR_EL3_Type_TFP w__12) == 1#1) : Bool)
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
      if ((HaveEL EL3) : Bool)
      then
        (do
          let w__13 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_EZ w__13) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


def IsSMEEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  let disabled ← (( do (undefined_bool_at (← occLabel 621) ()) ) : SailME Bool Bool )
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
            let b__0 := (_get_CPACR_EL1_Type_SMEN w__3)
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
              let b__1 := (_get_CPTR_EL2_Type_SMEN w__9)
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
              if (((_get_CPTR_EL2_Type_TSM w__12) == 1#1) : Bool)
              then
                (do
                  SailME.throw (false : Bool))
              else (pure (()))))
      else (pure (()))
      if ((HaveEL EL3) : Bool)
      then
        (do
          let w__13 ← (( do readReg CPTR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_CPTR_EL3_Type_ESM w__13) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


end ArmFull.Functions
