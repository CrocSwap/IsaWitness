import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0012
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179

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

def EffectiveSCR_EL3_NS (_ : Unit) : SailM (BitVec 1) := do
  let w__0 ← (( do (HaveSecureState ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (1#1))
  else
    (do
      if ((! (HaveEL EL3)) : Bool)
      then (pure (0#1))
      else
        (do
          let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
          (pure ((_get_SCR_EL3_Type_NS w__1)))))


def ExternalSecureNoninvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((! (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (SecureOnlyImplementation ()) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do (HaveNoninvasiveDebugAuth ()) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          if ((← do
               (ExternalNoninvasiveDebugEnabled ())) : Bool)
          then
            (do
              if ((← do
                   let w__4 ← (( do readReg SPIDEN ) : SailM Signal )
                   (pure (((BEq.beq w__4 Signal_High) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__5 ← (( do readReg SPNIDEN ) : SailM Signal )
                  (pure (((BEq.beq w__5 Signal_High) : Bool)))))
          else (pure false))
      else
        (do
          (ExternalSecureInvasiveDebugEnabled ())))


def ExternalRootInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           if ((← do
                if ((← do
                     (ExternalInvasiveDebugEnabled ())) : Bool)
                then
                  (do
                    if ((← do
                         let w__2 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                         (pure (((! w__2) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        (ExternalSecureInvasiveDebugEnabled ())))
                else (pure false)) : Bool)
           then
             (do
               (ExternalRealmInvasiveDebugEnabled ()))
           else (pure false)) : Bool)
      then
        (do
          let w__8 ← (( do readReg RTPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__8 Signal_High) : Bool))))
      else (pure false))


def GetBRBENumRecords (_ : Unit) : SailM Int := do
  let w__6 ← (( do
    if ((← do
         let w__0 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
         (pure ((((BitVec.toNat (_get_BRBIDR0_EL1_Type_NUMREC w__0)) == (BitVec.toNat 0x08#8)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
             (pure ((((BitVec.toNat (_get_BRBIDR0_EL1_Type_NUMREC w__1)) == (BitVec.toNat 0x10#8)) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__2 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
                 (pure ((((BitVec.toNat (_get_BRBIDR0_EL1_Type_NUMREC w__2)) == (BitVec.toNat 0x20#8)) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__3 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
                (pure ((((BitVec.toNat (_get_BRBIDR0_EL1_Type_NUMREC w__3)) == (BitVec.toNat 0x40#8)) : Bool))))))
    ) : SailM Bool )
  ArmFull.assert w__6 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6426.176-6426.177"
  (__IMPDEF_integer "Number of BRB records")


def DoubleLockStatus (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveDoubleLock ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          if ((← do
               if ((← do
                    let w__2 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                    (pure ((((_get_DBGOSDLR_Type_DLK w__2) == 1#1) : Bool)))) : Bool)
               then
                 (do
                   let w__3 ← (( do (DBGPRCR_read ()) ) : SailM (BitVec 32) )
                   (pure ((((_get_DBGPRCR_Type_CORENPDRQ w__3) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (Halted ()) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false))
      else
        (do
          if ((← do
               if ((← do
                    let w__7 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
                    (pure ((((_get_OSDLR_EL1_Type_DLK w__7) == 1#1) : Bool)))) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
                   (pure ((((_get_DBGPRCR_EL1_Type_CORENPDRQ w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__10 ← (( do (Halted ()) ) : SailM Bool )
              (pure (((! w__10) : Bool))))
          else (pure false)))


def DebugTargetFrom (from_state : SecurityState) : SailM (BitVec 2) := do
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 650) ()) ) : SailM Bool )
  let w__5 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        if (((bne from_state SS_Secure) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (HaveSecureEL2Ext ())) : Bool)
            then
              (do
                if (((! (HaveEL EL3)) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_EEL2 w__1) == 1#1) : Bool)))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        if (w__6 : Bool)
        then
          (do
            if ((← do
                 let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((_get_HDCR_Type_TDE w__7) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_TGE w__8) == 1#1) : Bool)))))
        else
          (do
            if ((← do
                 let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_MDCR_EL2_Type_TDE w__10) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__11) == 1#1) : Bool))))))
    else (pure (false)) ) : SailM Bool )
  let target ← (( do (undefined_bitvector_at (← occLabel 651) 2) ) : SailM (BitVec 2) )
  if (route_to_el2 : Bool)
  then (pure (EL2))
  else
    (do
      let w__15 ← (( do
        (pure ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__13 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  (pure (((! w__13) : Bool))))
              else (pure false)) && ((BEq.beq from_state SS_Secure) : Bool))) ) : SailM Bool )
      let target : (BitVec 2) :=
        if (w__15 : Bool)
        then EL3
        else EL1
      (pure (target)))


def IsVirtualSErrorPending (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (pure (((_get_HCR_Type_VA w__1) == 1#1))))
  else
    (do
      let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_HCR_EL2_Type_VSE w__2) == 1#1))))


def ClearPendingVirtualSError (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VA w__1 0#1)))
  else
    (do
      let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__2 8 8 0#1))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPDefaultNaN (N : Nat) : SailM (BitVec N) := do
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr N))


def AArch64_PAMax (_ : Unit) : SailM Int := do
  let pamax ← (( do (__IMPDEF_integer "Maximum Physical Address Size") ) : SailM Int )
  ArmFull.assert ((pamax == 32) || ((pamax == 36) || ((pamax == 40) || ((pamax == 42) || ((pamax == 44) || ((pamax == 48) || ((pamax == 52) || (pamax == 56)))))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:19468.120-19468.121"
  (pure (pamax))


def RegimeUsingAArch32 (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL10 =>
    (do
      (ELUsingAArch32 EL1))
  | .Regime_EL30 => (pure (true))
  | .Regime_EL20 => (pure (false))
  | .Regime_EL2 =>
    (do
      (ELUsingAArch32 EL2))
  | .Regime_EL3 => (pure (false))


def AArch64_S1TTWParamsEL3 (_ : Unit) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1273) ()) ) : SailM S1TTWParams )
  let w__0 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let w__1 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL3_Type_TG0 w__0)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__1 } : S1TTWParams)
  let w__2 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_TCR_EL3_Type_T0SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL3_Type_PS w__3) } : S1TTWParams)
  let w__4 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_TCR_EL3_Type_IRGN0 w__4) } : S1TTWParams)
  let w__5 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_TCR_EL3_Type_ORGN0 w__5) } : S1TTWParams)
  let w__6 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_TCR_EL3_Type_SH0 w__6) } : S1TTWParams)
  let w__7 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with tbi := (_get_TCR_EL3_Type_TBI w__7) } : S1TTWParams)
  let w__8 ← (( do readReg MAIR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__8) } : S1TTWParams)
  let w__9 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg MAIR2_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__10) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__11 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let w__13 ← (( do
    if (w__11 : Bool)
    then
      (do
        let w__12 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_AIE w__12))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__13 } : S1TTWParams)
  let w__14 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL3_Type_WXN w__14) } : S1TTWParams)
  let w__15 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL3_Type_EE w__15) } : S1TTWParams)
  let w__18 ← (( do
    if ((← do
         let w__16 ← (( do (HaveRME ()) ) : SailM Bool )
         (pure (((! w__16) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (HaveSecureEL2Ext ())) ) : SailM Bool )
  let w__20 ← (( do
    if (w__18 : Bool)
    then
      (do
        let w__19 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_SCR_EL3_Type_SIF w__19))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with sif := w__20 } : S1TTWParams)
  let w__21 ← (( do (HavePACExt ()) ) : SailM Bool )
  let w__23 ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_TBID w__22))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tbid := w__23 } : S1TTWParams)
  let w__24 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
  let w__26 ← (( do
    if (w__24 : Bool)
    then
      (do
        let w__25 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HPD w__25))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hpd := w__26 } : S1TTWParams)
  let w__27 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__29 ← (( do
    if (w__27 : Bool)
    then
      (do
        let w__28 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HA w__28))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__29 } : S1TTWParams)
  let w__30 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__32 ← (( do
    if (w__30 : Bool)
    then
      (do
        let w__31 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_HD w__31))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__32 } : S1TTWParams)
  let w__34 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__34 : Bool)
    then
      (do
        let w__35 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_TCR_EL3_Type_DS w__35) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__36 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__38 ← (( do
    if (w__36 : Bool)
    then
      (do
        let w__37 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_D128 w__37))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__38 } : S1TTWParams)
  let w__40 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__39 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TTBR0_EL3_Type_SKL w__39))))
    else (pure (0b00#2)) ) : SailM (BitVec 2) )
  let walkparams := ({ walkparams with skl := w__40 } : S1TTWParams)
  let w__42 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__41 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_DisCH0 w__41))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with disch := w__42 } : S1TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S1TTWParams := { walkparams with pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__43 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
        let w__45 ← (( do
          if (w__43 : Bool)
          then
            (do
              let w__44 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL3_Type_PIE w__44))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__45 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__46 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__46 : Bool)
    then
      (do
        let w__47 ← (( do readReg PIR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__47) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__48 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
  let w__50 ← (( do
    if (w__48 : Bool)
    then
      (do
        let w__49 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL3_Type_MTX w__49))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with mtx := w__50 } : S1TTWParams)
  let w__52 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 == 0#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__52 : Bool)
    then
      (do
        let w__53 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pnch := (_get_TCR_EL3_Type_PnCH w__53) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__55 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  let walkparams ← (( do
    if (w__55 : Bool)
    then
      (do
        let w__56 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with haft := (_get_TCR_EL3_Type_HAFT w__56) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__57 ← (( do (HaveFeatMEC ()) ) : SailM Bool )
  let w__59 ← (( do
    if (w__57 : Bool)
    then
      (do
        let w__58 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL3_Type_EMEC w__58))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__59 } : S1TTWParams)
  (pure (walkparams))


def NumBreakpointsImplemented (_ : Unit) : SailM Int := do
  (__IMPDEF_integer "Number of breakpoints")


def NumWatchpointsImplemented (_ : Unit) : SailM Int := do
  (__IMPDEF_integer "Number of watchpoints")


/-- Type quantifiers: k_ex10456193_ : Bool -/
def C27bReservedControl (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (isbreakpnt : Bool) : SailM Bool := SailME.run do
  let w__0 ← (( do (HaveRME ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then
    (do
      if ((ssce_in != 0#1) : Bool)
      then
        (do
          SailME.throw (true : Bool))
      else (pure (())))
  else (pure (()))
  let reserved : Bool := false
  let ssc : (BitVec 2) := ssc_in
  let ssce : (BitVec 1) := ssce_in
  let hmc : (BitVec 1) := hmc_in
  let pxc : (BitVec 2) := pxc_in
  let reserved ← (( do
    match (BitVec.setWidth 6 (((hmc +++ ssce) +++ ssc) +++ pxc)) with
    | 0b001110 => (pure (true))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__1 ← (( do (HaveSecureState ()) ) : SailME Bool Bool )
            let reserved := ((! w__1) : Bool)
            (pure (reserved)))
        else
          (let reserved : Bool :=
            if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 5 2)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else
              (match b__0 with
              | 0b100110 => true
              | b__0 =>
                (if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                then true
                else
                  (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (1#1 : (BitVec 1))) : Bool)
                  then
                    ((ssc != 0b01#2) || (((hmc +++ pxc) == 0b000#3) || ((hmc +++ pxc) == 0b110#3)))
                  else false)))
          (pure (reserved)))) ) : SailME Bool Bool )
  let reserved : Bool :=
    if (((((! isbreakpnt) || (! (HaveAArch32EL EL1))) && ((hmc +++ pxc) == 0b000#3)) && (ssc != 0b11#2)) : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if ((((! (HaveEL EL3)) && (! (HaveEL EL2))) && ((hmc != 0#1) || (ssc != 0b00#2))) : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if ((((! (HaveEL EL3)) && ((ssc == 0b01#2) || (ssc == 0b10#2))) && (((hmc +++ ssc) +++ pxc) != 0b10100#5)) : Bool)
    then true
    else reserved
  let w__4 ← (( do
    (pure ((← do
          if (((! (HaveEL EL3)) : Bool) : Bool)
          then (pure true)
          else
            (do
              let w__2 ← (( do (HaveAArch64 ()) ) : SailME Bool Bool )
              (pure (((! w__2) : Bool))))) && ((((hmc +++ ssc) +++ pxc) == 0b11000#5) : Bool))) ) :
    SailME Bool Bool )
  let reserved : Bool :=
    if (w__4 : Bool)
    then true
    else reserved
  let reserved : Bool :=
    if (((! (HaveEL EL2)) && (((hmc +++ ssc) +++ pxc) == 0b11100#5)) : Bool)
    then true
    else reserved
  let w__6 ← (( do
    (pure ((← do
          let w__5 ← (( do (HaveSecureEL2Ext ()) ) : SailME Bool Bool )
          (pure (((! w__5) : Bool)))) && (match (BitVec.setWidth 5 ((hmc +++ ssc) +++ pxc)) with
        | 0b01100 => true
        | 0b10100 => true
        | b__4 =>
          (if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__4 3 2)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   b__4 0 0)) == (1#1 : (BitVec 1)))) : Bool)
          then true
          else false) : Bool))) ) : SailME Bool Bool )
  let reserved : Bool :=
    if (w__6 : Bool)
    then true
    else reserved
  (pure (reserved))


def AArch64_BlockBBMSupportLevel (_ : Unit) : SailM Int := do
  let w__0 ← (( do (HaveBlockBBM ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__UNKNOWN_integer ()))
  else
    (do
      (__IMPDEF_integer "Block BBM support level"))


def AArch64_S2DecodeTG0 (tg0_in : (BitVec 2)) : SailM TGx := do
  let tg0 : (BitVec 2) := tg0_in
  let tgx ← (( do (undefined_TGx (← occLabel 1502) ()) ) : SailM TGx )
  let tg0 ← (( do
    if ((tg0 == 0b11#2) : Bool)
    then
      (do
        (__IMPDEF_bits 2 "TG0 encoded granule size"))
    else (pure (tg0)) ) : SailM (BitVec 2) )
  let tgx : TGx :=
    match tg0 with
    | 0b00 => TGx_4KB
    | 0b01 => TGx_64KB
    | 0b10 => TGx_16KB
    | _ => tgx
  let w__1 ← (( do (AArch64_HaveS2TG tgx) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let w__2 ← (( do (__IMPDEF_bits 2 "TG0 encoded granule size") ) : SailM (BitVec 2) )
      let tgx : TGx :=
        match w__2 with
        | 0b00 => TGx_4KB
        | 0b01 => TGx_64KB
        | 0b10 => TGx_16KB
        | _ => tgx
      (pure (tgx)))
  else (pure (tgx))


end ArmFull.Functions
