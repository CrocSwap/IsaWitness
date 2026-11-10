import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049

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

def _set_CNTHP_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHP_CTL_Type_IMASK r v)


def _set_CNTHVS_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_IMASK r v)


def _set_CNTHVS_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_IMASK r v)


def _set_CNTHV_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_IMASK r v)


def _set_CNTHV_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHV_CTL_Type_IMASK r v)


def _set_CNTPS_CTL_EL1_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_IMASK r v)


def _set_CNTP_CTL_EL0_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_IMASK r v)


def _set_CNTP_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTP_CTL_Type_IMASK r v)


def _set_CNTV_CTL_EL0_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_IMASK r v)


def _set_CNTV_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTV_CTL_Type_IMASK r v)


def _set_CNTHP_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_ISTATUS r v)


def _set_CNTHPS_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_ISTATUS r v)


def _set_CNTHPS_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_ISTATUS r v)


def _set_CNTHP_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHP_CTL_Type_ISTATUS r v)


def _set_CNTHVS_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_ISTATUS r v)


def _set_CNTHVS_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_ISTATUS r v)


def _set_CNTHV_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_ISTATUS r v)


def _set_CNTHV_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHV_CTL_Type_ISTATUS r v)


def _set_CNTPS_CTL_EL1_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_ISTATUS r v)


def _set_CNTP_CTL_EL0_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_ISTATUS r v)


def _set_CNTP_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTP_CTL_Type_ISTATUS r v)


def _set_CNTV_CTL_EL0_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_ISTATUS r v)


def _set_CNTV_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTV_CTL_Type_ISTATUS r v)


def _set_CNTHP_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_CVAL_EL2_Type_CompareValue r v)


def _set_CNTHPS_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHPS_CVAL_EL2_Type_CompareValue r v)


def _set_CNTHP_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_CVAL_Type_CompareValue r v)


def _set_CNTHVS_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHVS_CVAL_EL2_Type_CompareValue r v)


def _set_CNTHV_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHV_CVAL_EL2_Type_CompareValue r v)


def _set_CNTPS_CVAL_EL1_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTPS_CVAL_EL1_Type_CompareValue r v)


def _set_CNTP_CVAL_EL0_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_CVAL_EL0_Type_CompareValue r v)


def _set_CNTP_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_CVAL_Type_CompareValue r v)


def _set_CNTV_CVAL_EL0_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_CVAL_EL0_Type_CompareValue r v)


def _set_CNTV_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_CVAL_Type_CompareValue r v)


def IsTimerConditionMet (offset : (BitVec 64)) (compare_value : (BitVec 64)) (imask : (BitVec 1)) (intid : InterruptID) : SailM Bool := do
  let w__0 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
  let condition_met : Bool :=
    (((BitVec.toNat (w__0 - offset)) -i (BitVec.toNat compare_value)) ≥b 0)
  let level : Signal :=
    if ((condition_met && (imask == 0#1)) : Bool)
    then Signal_High
    else Signal_Low
  (SetInterruptRequestLevel intid level)
  (pure (condition_met))


def _set_CNTCR_Type_FCREQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 10)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTCR_Type_FCREQ r v)


def _set_CNTCR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTCR_Type_HDBG r v)


def _set_AMCFGR_EL0_Type_HDBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_HDBG r v)


def _set_AMCFGR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCFGR_Type_HDBG r v)


def _set_AMCR_EL0_Type_HDBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCR_EL0_Type_HDBG r v)


def _set_AMCR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCR_Type_HDBG r v)


def _set_CNTCR_Type_SCEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTCR_Type_SCEN r v)


def _set_CNTSCR_Type_ScaleVal (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTSCR_Type_ScaleVal r v)


def PAREncodeShareability (memattrs : MemoryAttributes) : (BitVec 2) :=
  if (((BEq.beq memattrs.memtype MemType_Device) || ((memattrs.inner.attrs == MemAttr_NC) && (memattrs.outer.attrs == MemAttr_NC))) : Bool)
  then 0b10#2
  else
    (match memattrs.shareability with
    | .Shareability_NSH => 0b00#2
    | .Shareability_ISH => 0b11#2
    | .Shareability_OSH => 0b10#2)


def ConstrainUnpredictable (which : Unpredictable) : SailM Constraint := do
  match which with
  | .Unpredictable_ALUEXCEPTIONRETURN =>
    (do
      (C47PickALUEXCEPTIONRETURN ()))
  | .Unpredictable_BASEOVERLAP =>
    (do
      (C47PickBASEOVERLAP ()))
  | .Unpredictable_BPNOTCTXCMP =>
    (do
      (C47PickBPNOTCTXCMP ()))
  | .Unpredictable_BPNOTIMPL =>
    (do
      (C47PickBPNOTIMPL ()))
  | .Unpredictable_DATAOVERLAP =>
    (do
      (C47PickDATAOVERLAP ()))
  | .Unpredictable_DEVICETAGSTORE =>
    (do
      (C47PickDEVICETAGSTORE ()))
  | .Unpredictable_DEVPAGE2 =>
    (do
      (C47PickDEVPAGE2 ()))
  | .Unpredictable_INSTRDEVICE =>
    (do
      (C47PickINSTRDEVICE ()))
  | .Unpredictable_LDPOVERLAP =>
    (do
      (C47PickLDPOVERLAP ()))
  | .Unpredictable_LS64UNSUPPORTED =>
    (do
      (C47PickLS64UNSUPPORTED ()))
  | .Unpredictable_MOPSOVERLAP31 =>
    (do
      (C47PickMOPSOVERLAP31 ()))
  | .Unpredictable_NVNV1 =>
    (do
      (C47PickNVNV1 ()))
  | .Unpredictable_RESBPMASK =>
    (do
      (C47PickRESBPMASK ()))
  | .Unpredictable_RESTnSZ =>
    (do
      (C47PickRESTnSZ ()))
  | .Unpredictable_RESWPMASK =>
    (do
      (C47PickRESWPMASK ()))
  | .Unpredictable_S2RESMEMATTR =>
    (do
      (C47PickS2RESMEMATTR ()))
  | .Unpredictable_SMD =>
    (do
      (C47PickSMD ()))
  | .Unpredictable_Shareability =>
    (do
      (C47PickShareability ()))
  | .Unpredictable_VMSR =>
    (do
      (C47PickVMSR ()))
  | .Unpredictable_WBOVERLAPLD =>
    (do
      (C47PickWBOVERLAPLD ()))
  | .Unpredictable_WBOVERLAPST =>
    (do
      (C47PickWBOVERLAPST ()))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/armcert-defects/c47-accepted/armcert-c47.sail:156.25-156.26"
      throw Error.Exit)


def EffectiveShareability (memattrs : MemoryAttributes) : Shareability :=
  if (((BEq.beq memattrs.memtype MemType_Device) || ((memattrs.inner.attrs == MemAttr_NC) && (memattrs.outer.attrs == MemAttr_NC))) : Bool)
  then Shareability_OSH
  else memattrs.shareability


def DecodeDevice (device : (BitVec 2)) : SailM DeviceType := do
  match device with
  | 0b00 => (pure (DeviceType_nGnRnE))
  | 0b01 => (pure (DeviceType_nGnRE))
  | 0b10 => (pure (DeviceType_nGRE))
  | 0b11 => (pure (DeviceType_GRE))
  | _ =>
    (do
      (undefined_DeviceType (← occLabel 1211) ()))


def DecodeSDFAttr (rgn : (BitVec 2)) : SailM MemAttrHints := do
  let sdfattr ← (( do (undefined_MemAttrHints (← occLabel 1212) ()) ) : SailM MemAttrHints )
  let sdfattr : MemAttrHints :=
    match rgn with
    | 0b00 => { sdfattr with attrs := MemAttr_NC }
    | 0b01 =>
      (let sdfattr : MemAttrHints := { sdfattr with attrs := MemAttr_WB }
      { sdfattr with hints := MemHint_RWA })
    | 0b10 =>
      (let sdfattr : MemAttrHints := { sdfattr with attrs := MemAttr_WT }
      { sdfattr with hints := MemHint_RA })
    | _ =>
      (let sdfattr : MemAttrHints := { sdfattr with attrs := MemAttr_WB }
      { sdfattr with hints := MemHint_RA })
  let sdfattr : MemAttrHints := { sdfattr with transient := false }
  (pure (sdfattr))


def DecodeLDFAttr (attr : (BitVec 4)) : SailM MemAttrHints := do
  let ldfattr ← (( do (undefined_MemAttrHints (← occLabel 1213) ()) ) : SailM MemAttrHints )
  let ldfattr ← (( do
    if ((let b__1 := attr
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 2 2)) == (0#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then
      (let ldfattr : MemAttrHints := { ldfattr with attrs := MemAttr_WT }
      (pure (ldfattr)))
    else
      (do
        if ((attr == 0b0100#4) : Bool)
        then
          (let ldfattr : MemAttrHints := { ldfattr with attrs := MemAttr_NC }
          (pure (ldfattr)))
        else
          (do
            if ((let b__0 := attr
               (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (1#1 : (BitVec 1))) : Bool)
               then true
               else false : Bool)) : Bool)
            then
              (let ldfattr : MemAttrHints := { ldfattr with attrs := MemAttr_WB }
              (pure (ldfattr)))
            else
              (do
                (Unreachable ())
                (pure (ldfattr))))) ) : SailM MemAttrHints )
  let ldfattr : MemAttrHints :=
    if ((ldfattr.attrs != MemAttr_NC) : Bool)
    then
      (match (BitVec.setWidth 2 (Sail.BitVec.extractLsb attr 1 0)) with
      | 0b00 => { ldfattr with hints := MemHint_No }
      | 0b01 => { ldfattr with hints := MemHint_WA }
      | 0b10 => { ldfattr with hints := MemHint_RA }
      | _ => { ldfattr with hints := MemHint_RWA })
    else ldfattr
  let ldfattr : MemAttrHints :=
    if (((ldfattr.attrs != MemAttr_NC) && (ldfattr.hints != MemHint_No)) : Bool)
    then
      { ldfattr with transient := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access attr 3)])) == 0#1) }
    else ldfattr
  (pure (ldfattr))


def S2CombineS1AttrHints (s1_attrhints : MemAttrHints) (s2_attrhints : MemAttrHints) : SailM MemAttrHints := do
  let attrhints ← (( do (undefined_MemAttrHints (← occLabel 1215) ()) ) : SailM MemAttrHints )
  let attrhints : MemAttrHints :=
    if (((s1_attrhints.attrs == MemAttr_NC) || (s2_attrhints.attrs == MemAttr_NC)) : Bool)
    then { attrhints with attrs := MemAttr_NC }
    else
      (if (((s1_attrhints.attrs == MemAttr_WT) || (s2_attrhints.attrs == MemAttr_WT)) : Bool)
      then { attrhints with attrs := MemAttr_WT }
      else { attrhints with attrs := MemAttr_WB })
  let attrhints : MemAttrHints :=
    if ((attrhints.attrs != MemAttr_NC) : Bool)
    then
      (let attrhints : MemAttrHints := { attrhints with hints := s1_attrhints.hints }
      { attrhints with transient := s1_attrhints.transient })
    else attrhints
  (pure (attrhints))


def _set_GPCCR_EL3_Type_GPC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_GPC r v)


def _set_GPCCR_EL3_Type_GPCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_GPCP r v)


def _set_GPCCR_EL3_Type_L0GPTSZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_L0GPTSZ r v)


def _set_GPCCR_EL3_Type_ORGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_ORGN r v)


def _set_GPCCR_EL3_Type_PGS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_PGS r v)


def _set_GPCCR_EL3_Type_PPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GPCCR_EL3_Type_PPS r v)


def DecodePPS (_ : Unit) : SailM Int := do
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  match (BitVec.setWidth 3 (_get_GPCCR_EL3_Type_PPS w__0)) with
  | 0b000 => (pure (32))
  | 0b001 => (pure (36))
  | 0b010 => (pure (40))
  | 0b011 => (pure (42))
  | 0b100 => (pure (44))
  | 0b101 => (pure (48))
  | 0b110 => (pure (52))
  | _ =>
    (do
      (Unreachable ())
      (undefined_int_at (← occLabel 1223) ()))


def GPTL0Size (_ : Unit) : SailM Int := SailME.run do
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailME Int (BitVec 64) )
  match (BitVec.setWidth 4 (_get_GPCCR_EL3_Type_L0GPTSZ w__0)) with
  | 0b0000 =>
    (do
      SailME.throw (GPTRange_1GB : Int))
  | 0b0100 =>
    (do
      SailME.throw (GPTRange_16GB : Int))
  | 0b0110 =>
    (do
      SailME.throw (GPTRange_64GB : Int))
  | 0b1001 =>
    (do
      SailME.throw (GPTRange_512GB : Int))
  | _ =>
    (do
      (Unreachable ()))
  (pure (30))


def DecodePGS (pgs : (BitVec 2)) : SailM PGSe := do
  match pgs with
  | 0b00 => (pure (PGS_4KB))
  | 0b10 => (pure (PGS_16KB))
  | 0b01 => (pure (PGS_64KB))
  | _ =>
    (do
      (Unreachable ())
      (undefined_PGSe (← occLabel 1231) ()))


def CreatePhysMemRetStatus (fault : Fault) : PhysMemRetStatus :=
  { statuscode := fault
    extflag := 0#1
    merrorstate := ErrorState_Uncategorized
    store64bstatus := (Zeros (n := 64)) }


def __GIC_InterruptID (intid : InterruptID) : (BitVec 32) :=
  let PPI_OFFSET : Nat := 16
  match intid with
  | .InterruptID_CNTP => (BitVec.addInt 0x0000000D#32 PPI_OFFSET)
  | .InterruptID_CNTHP => (BitVec.addInt 0x0000000A#32 PPI_OFFSET)
  | .InterruptID_CNTV => (BitVec.addInt 0x0000000B#32 PPI_OFFSET)
  | _ => GIC_PENDING_NONE


/-- Type quantifiers: size : Nat, size > 0 -/
def read_request (accdesc : AccessDescriptor) (ti : (Option TranslationInfo)) (size : Nat) (va : (BitVec 64)) (pa : (BitVec 56)) : (Mem_read_request size 64 (BitVec 56) (Option TranslationInfo) arm_acc_type) :=
  { access_kind := (AccessDescriptor_to_Access_kind accdesc)
    va := (some va)
    pa := pa
    translation := ti
    size := size
    tag := false }


def __GICD_TYPER :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Zeros (n := 32)) 10 10 1#1) 4 0 0b00111#5)


/-- Type quantifiers: n : Nat, n > 0 -/
def __ReadUART (offset : (BitVec 16)) (n : Nat) : (BitVec (8 * n)) :=
  match offset with
  | _ =>
    (let _ : Unit := (prerr_bits "[UART] Unknown read offset: " offset)
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((8 *i n)))))))


def TLBIncludesGPT (context : TLBContext) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: level : Int -/
def TranslationSize (d128 : (BitVec 1)) (tgx : TGx) (level : Int) : Int :=
  let granulebits : Int := (TGxGranuleBits tgx)
  let descsizelog2 : Int :=
    if ((d128 == 1#1) : Bool)
    then 4
    else 3
  let blockbits : Int := ((FINAL_LEVEL -i level) *i (granulebits -i descsizelog2))
  (granulebits +i blockbits)


def DecodePASpace (nse : (BitVec 1)) (ns : (BitVec 1)) : SailM PASpace := do
  match (BitVec.setWidth 2 (nse +++ ns)) with
  | 0b00 => (pure (PAS_Secure))
  | 0b01 => (pure (PAS_NonSecure))
  | 0b10 => (pure (PAS_Root))
  | 0b11 => (pure (PAS_Realm))
  | _ =>
    (do
      (undefined_PASpace (← occLabel 1248) ()))


def _set_TCR2_EL1_Type_DisCH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_DisCH1 r v)


def _set_TCR2_EL2_Type_DisCH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_DisCH1 r v)


def _set_TCR2_EL2_Type_AMEC0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_AMEC0 r v)


def _set_TCR2_EL2_Type_AMEC1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_AMEC1 r v)


def _set_TCR2_EL2_Type_SKL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_SKL0 r v)


def _set_TCR2_EL2_Type_SKL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_SKL1 r v)


def PACInvSub (Tinput : (BitVec 64)) : SailM (BitVec 64) := do
  let Toutput ← (( do (undefined_bitvector_at (← occLabel 1277) 64) ) : SailM (BitVec 64) )
  let Toutput ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 15
    (do
      let mut loop_vars := Toutput
      for i in [loop_i_lower:loop_i_upper:1]i do
        let Toutput := loop_vars
        loop_vars :=
          match (BitVec.setWidth 4 (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb Tinput
            (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i)))))) with
          | 0b0000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0101#4))
          | 0b0001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1110#4))
          | 0b0010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1101#4))
          | 0b0011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1000#4))
          | 0b0100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1010#4))
          | 0b0101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1011#4))
          | 0b0110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0001#4))
          | 0b0111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1001#4))
          | 0b1000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0010#4))
          | 0b1001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0110#4))
          | 0b1010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1111#4))
          | 0b1011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0000#4))
          | 0b1100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0100#4))
          | 0b1101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1100#4))
          | 0b1110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0111#4))
          | 0b1111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0011#4))
          | _ => Toutput
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (pure (Toutput))


def PACMult (Sinput : (BitVec 64)) : SailM (BitVec 64) := do
  let t0 ← (( do (undefined_bitvector_at (← occLabel 1279) 4) ) : SailM (BitVec 4) )
  let t1 ← (( do (undefined_bitvector_at (← occLabel 1280) 4) ) : SailM (BitVec 4) )
  let t2 ← (( do (undefined_bitvector_at (← occLabel 1281) 4) ) : SailM (BitVec 4) )
  let t3 ← (( do (undefined_bitvector_at (← occLabel 1282) 4) ) : SailM (BitVec 4) )
  let Soutput ← (( do (undefined_bitvector_at (← occLabel 1283) 64) ) : SailM (BitVec 64) )
  let (Soutput, t0, t1, t2, t3) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 3
    (do
      let mut loop_vars := (Soutput, t0, t1, t2, t3)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (Soutput, t0, t1, t2, t3) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 8)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 8)))))) 1) ) : SailM (BitVec 4) )
          let w__1 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 4)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 4)))))) 2) ) : SailM (BitVec 4) )
          let t0 := ((Sail.BitVec.updateSubrange t0 3 0 (w__0 ^^^ w__1)) : (BitVec 4))
          let w__2 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i))))) 1) )
            : SailM (BitVec 4) )
          let t0 :=
            ((Sail.BitVec.updateSubrange t0 3 0
              ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb t0 3 0)) ^^^ w__2)) : (BitVec 4))
          let w__3 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 12)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 12)))))) 1) ) : SailM (BitVec 4) )
          let w__4 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 4)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 4)))))) 1) ) : SailM (BitVec 4) )
          let t1 := ((Sail.BitVec.updateSubrange t1 3 0 (w__3 ^^^ w__4)) : (BitVec 4))
          let w__5 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i))))) 2) )
            : SailM (BitVec 4) )
          let t1 :=
            ((Sail.BitVec.updateSubrange t1 3 0
              ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb t1 3 0)) ^^^ w__5)) : (BitVec 4))
          let w__6 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 12)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 12)))))) 2) ) : SailM (BitVec 4) )
          let w__7 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 8)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 8)))))) 1) ) : SailM (BitVec 4) )
          let t2 := ((Sail.BitVec.updateSubrange t2 3 0 (w__6 ^^^ w__7)) : (BitVec 4))
          let w__8 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i))))) 1) )
            : SailM (BitVec 4) )
          let t2 :=
            ((Sail.BitVec.updateSubrange t2 3 0
              ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb t2 3 0)) ^^^ w__8)) : (BitVec 4))
          let w__9 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 12)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 12)))))) 1) ) : SailM (BitVec 4) )
          let w__10 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 8)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 8)))))) 2) ) : SailM (BitVec 4) )
          let t3 := ((Sail.BitVec.updateSubrange t3 3 0 (w__9 ^^^ w__10)) : (BitVec 4))
          let w__11 ← (( do
            (RotCell
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb Sinput
                (Sail.Int.toNatChecked (((4 *i (i +i 4)) +i 3)))
                (Sail.Int.toNatChecked ((4 *i (i +i 4)))))) 1) ) : SailM (BitVec 4) )
          let t3 :=
            ((Sail.BitVec.updateSubrange t3 3 0
              ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb t3 3 0)) ^^^ w__11)) : (BitVec 4))
          let Soutput : (BitVec 64) :=
            (Sail.BitVec.updateSubrange Soutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i)))
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb t3 3 0)))
          let Soutput : (BitVec 64) :=
            (Sail.BitVec.updateSubrange Soutput (Sail.Int.toNatChecked (((4 *i (i +i 4)) +i 3)))
              (Sail.Int.toNatChecked ((4 *i (i +i 4))))
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb t2 3 0)))
          let Soutput : (BitVec 64) :=
            (Sail.BitVec.updateSubrange Soutput (Sail.Int.toNatChecked (((4 *i (i +i 8)) +i 3)))
              (Sail.Int.toNatChecked ((4 *i (i +i 8))))
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb t1 3 0)))
          let Soutput : (BitVec 64) :=
            (Sail.BitVec.updateSubrange Soutput (Sail.Int.toNatChecked (((4 *i (i +i 12)) +i 3)))
              (Sail.Int.toNatChecked ((4 *i (i +i 12))))
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb t0 3 0)))
          (pure ((Soutput, t0, t1, t2, t3)))
      (pure loop_vars)) ) : SailM
    ((BitVec 64) × (BitVec 4) × (BitVec 4) × (BitVec 4) × (BitVec 4)) )
  (pure (Soutput))


end ArmFull.Functions
