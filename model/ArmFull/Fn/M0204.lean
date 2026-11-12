import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0052
import ArmFull.Fn.M0098
import ArmFull.Fn.M0100
import ArmFull.Fn.M0115
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0173
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0188
import ArmFull.Fn.M0189
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0198

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

def PtrHasUpperAndLowerAddRanges (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  (pure ((HasUnprivileged regime)))


def AArch64_AllocationTagAccessIsEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
          (pure ((((_get_SCR_EL3_Type_ATA w__0) == 0#1) : Bool)))) && (((el == EL0) || ((el == EL1) || (el == EL2))) : Bool)))
    ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let w__8 ← (( do
        if ((← do
             if ((← do
                  (pure ((← do
                        let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_ATA w__2) == 0#1) : Bool)))) && (((el == EL0) || (el == EL1)) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) != 0b11#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then (pure (false))
      else
        (do
          let regime ← (( do (TranslationRegime el) ) : SailM Regime )
          match regime with
          | .Regime_EL3 =>
            (do
              let w__9 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_SCTLR_EL3_Type_ATA w__9) == 1#1))))
          | .Regime_EL2 =>
            (do
              let w__10 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure (((_get_SCTLR_EL2_Type_ATA w__10) == 1#1))))
          | .Regime_EL20 =>
            (do
              if ((el == EL0) : Bool)
              then
                (do
                  let w__11 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL2_Type_ATA0 w__11) == 1#1))))
              else
                (do
                  let w__12 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL2_Type_ATA w__12) == 1#1)))))
          | .Regime_EL10 =>
            (do
              if ((el == EL0) : Bool)
              then
                (do
                  let w__14 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL1_Type_ATA0 w__14) == 1#1))))
              else
                (do
                  let w__15 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL1_Type_ATA w__15) == 1#1)))))
          | _ =>
            (do
              (Unreachable ())
              (undefined_bool_at (← occLabel 1347) ()))))


def AArch64_EffectiveTCF (el : (BitVec 2)) : SailM (BitVec 2) := do
  let tcf ← (( do (undefined_bitvector_at (← occLabel 1358) 2) ) : SailM (BitVec 2) )
  let regime ← (( do (TranslationRegime el) ) : SailM Regime )
  let tcf ← (( do
    match regime with
    | .Regime_EL3 =>
      (do
        let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
        let tcf := ((_get_SCTLR_EL3_Type_TCF w__0) : (BitVec 2))
        (pure (tcf)))
    | .Regime_EL2 =>
      (do
        let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        let tcf := ((_get_SCTLR_EL2_Type_TCF w__1) : (BitVec 2))
        (pure (tcf)))
    | .Regime_EL20 =>
      (do
        if ((el == EL0) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL2_Type_TCF0 w__2))))
        else
          (do
            let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL2_Type_TCF w__3)))))
    | .Regime_EL10 =>
      (do
        if ((el == EL0) : Bool)
        then
          (do
            let w__5 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL1_Type_TCF0 w__5))))
        else
          (do
            let w__6 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL1_Type_TCF w__6)))))
    | _ =>
      (do
        (Unreachable ())
        (pure (tcf))) ) : SailM (BitVec 2) )
  if ((tcf == 0b11#2) : Bool)
  then
    (do
      let w__8 ← (( do (HaveMTEAsymFaultExt ()) ) : SailM Bool )
      if ((! w__8) : Bool)
      then
        (do
          let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_RESTCF 2) ) : SailM
            (Constraint × (BitVec 2)) )
          (pure (__tup_1)))
      else (pure (tcf)))
  else (pure (tcf))


def HaltOnBreakpointOrWatchpoint (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            (HaltingAllowed ())) : Bool)
       then
         (do
           let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
           (pure ((((_get_EDSCR_Type_HDE w__1) == 1#1) : Bool))))
       else (pure false)) : Bool)
  then
    (do
      let w__3 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      (pure ((((_get_OSLSR_EL1_Type_OSLK w__3) == 0#1) : Bool))))
  else (pure false)


def AArch64_S1ComputePermissions (regime : Regime) (walkstate : TTWState) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) : SailM S1AccessControls := do
  let s1overlay_perms ← (( do (undefined_S1AccessControls (← occLabel 1454) ()) ) : SailM
    S1AccessControls )
  let permissions : Permissions := walkstate.permissions
  let s1perms ← (( do (undefined_S1AccessControls (← occLabel 1455) ()) ) : SailM
    S1AccessControls )
  let s1perms ← (( do
    if ((walkparams.pie == 1#1) : Bool)
    then
      (do
        (AArch64_S1IndirectBasePermissions regime walkstate walkparams accdesc))
    else
      (do
        (AArch64_S1DirectBasePermissions regime walkstate walkparams accdesc)) ) : SailM
    S1AccessControls )
  let w__3 ← (( do
    if (((accdesc.el == EL0) : Bool) : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_S1E0POEnabled regime walkparams.nv1) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let s1perms ← (( do
    if (w__3 : Bool)
    then
      (let s1perms : S1AccessControls := { s1perms with overlay := false }
      (pure (s1perms)))
    else
      (do
        let w__5 ← (( do
          if (((accdesc.el != EL0) : Bool) : Bool)
          then
            (do
              let w__4 ← (( do (AArch64_S1POEnabled regime) ) : SailM Bool )
              (pure (((! w__4) : Bool))))
          else (pure false) ) : SailM Bool )
        let s1perms : S1AccessControls :=
          if (w__5 : Bool)
          then { s1perms with overlay := false }
          else s1perms
        (pure (s1perms))) ) : SailM S1AccessControls )
  let s1perms ← (( do
    if (s1perms.overlay : Bool)
    then
      (do
        let s1overlay_perms ← (( do (AArch64_S1OverlayPermissions regime walkstate accdesc) ) :
          SailM S1AccessControls )
        let s1perms : S1AccessControls := { s1perms with or := s1overlay_perms.or }
        let s1perms : S1AccessControls := { s1perms with ow := s1overlay_perms.ow }
        let s1perms : S1AccessControls := { s1perms with ox := s1overlay_perms.ox }
        (pure (s1perms)))
    else (pure (s1perms)) ) : SailM S1AccessControls )
  let s1perms : S1AccessControls :=
    if (((s1perms.overlay && (s1perms.wxn == 1#1)) && (s1perms.ox == 1#1)) : Bool)
    then { s1perms with ow := 0#1 }
    else
      (if ((s1perms.wxn == 1#1) : Bool)
      then { s1perms with x := 0#1 }
      else s1perms)
  (pure (s1perms))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S1ApplyOutputPerms (permissions_in : Permissions) (descriptor : (BitVec k_N)) (regime : Regime) (walkparams : S1TTWParams) : SailM Permissions := do
  let bit_index ← (( do (undefined_int_at (← occLabel 1484) ()) ) : SailM Int )
  let permissions : Permissions := permissions_in
  let pi_index ← (( do (undefined_bitvector_at (← occLabel 1485) 4) ) : SailM (BitVec 4) )
  let permissions ← (( do
    if ((walkparams.pie == 1#1) : Bool)
    then
      (do
        let pi_index ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25368.39-25368.40"
              let pi_index : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 118 115)
              (pure (pi_index)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25371.38-25371.39"
              let pi_index : (BitVec 4) :=
                (((Sail.BitVec.extractLsb descriptor 54 53) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        descriptor 51)]))) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 6)])))
              (pure (pi_index))) ) : SailM (BitVec 4) )
        let bit_index : Int := (4 *i (BitVec.toNat pi_index))
        let permissions : Permissions :=
          { permissions with ppi := (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
              walkparams.pir (Sail.Int.toNatChecked ((bit_index +i 3)))
              (Sail.Int.toNatChecked (bit_index)))) }
        let permissions : Permissions :=
          { permissions with upi := (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
              walkparams.pire0 (Sail.Int.toNatChecked ((bit_index +i 3)))
              (Sail.Int.toNatChecked (bit_index)))) }
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25377.33-25377.34"
        let permissions : Permissions :=
          { permissions with ndirty := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) }
        (pure (permissions)))
    else
      (do
        let w__2 ← (( do
          (pure ((← do
                if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                then
                  (do
                    (EL2Enabled ()))
                else (pure false)) && ((walkparams.nv1 == 1#1) : Bool))) ) : SailM Bool )
        let permissions ← (( do
          if (w__2 : Bool)
          then
            (do
              ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25381.37-25381.38"
              let permissions : Permissions :=
                { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) +++ 0#1)) }
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25383.38-25383.39"
              let permissions : Permissions :=
                { permissions with pxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 54)])) }
              (pure (permissions)))
          else
            (do
              if ((HasUnprivileged regime) : Bool)
              then
                (do
                  ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25386.37-25386.38"
                  let permissions : Permissions :=
                    { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                        (Sail.BitVec.extractLsb descriptor 7 6)) }
                  ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25388.38-25388.39"
                  let permissions : Permissions :=
                    { permissions with uxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 54)])) }
                  let permissions : Permissions :=
                    { permissions with pxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 53)])) }
                  (pure (permissions)))
              else
                (do
                  ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25392.37-25392.38"
                  let permissions : Permissions :=
                    { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) +++ 1#1)) }
                  ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25394.38-25394.39"
                  let permissions : Permissions :=
                    { permissions with xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 54)])) }
                  (pure (permissions)))) ) : SailM Permissions )
        ArmFull.assert (51 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25397.34-25397.35"
        let permissions : Permissions :=
          if ((((walkparams.ha == 1#1) && (walkparams.hd == 1#1)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     descriptor 51)])) == 1#1)) : Bool)
          then { permissions with ap := (BitVec.update permissions.ap 2 (Bit 0#1)) }
          else permissions
        (pure (permissions))) ) : SailM Permissions )
  let poe ← (( do (AArch64_S1POEnabled regime) ) : SailM Bool )
  let e0poe ← (( do
    if (((HasUnprivileged regime) : Bool) : Bool)
    then
      (do
        (AArch64_S1E0POEnabled regime walkparams.nv1))
    else (pure false) ) : SailM Bool )
  if ((poe || e0poe) : Bool)
  then
    (do
      if ((walkparams.d128 == 1#1) : Bool)
      then
        (do
          ArmFull.assert (124 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25407.39-25407.40"
          let permissions : Permissions :=
            { permissions with po_index := (Sail.BitVec.extractLsb descriptor 124 121) }
          (pure (permissions)))
      else
        (do
          ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25410.38-25410.39"
          let permissions : Permissions :=
            { permissions with po_index := (0#1 +++ (Sail.BitVec.extractLsb descriptor 62 60)) }
          (pure (permissions))))
  else (pure (permissions))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_GetS2TTWParams (ss : SecurityState) (ipaspace : PASpace) (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1508) ()) ) : SailM S2TTWParams )
  if ((BEq.beq ss SS_NonSecure) : Bool)
  then
    (do
      (AArch64_NSS2TTWParams s1aarch64))
  else
    (do
      let w__2 ← (( do
        (pure ((← do
              (HaveSecureEL2Ext ())) && ((BEq.beq ss SS_Secure) : Bool))) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          (AArch64_SS2TTWParams ipaspace s1aarch64))
      else
        (do
          if ((BEq.beq ss SS_Realm) : Bool)
          then
            (do
              (AArch64_RLS2TTWParams s1aarch64))
          else
            (do
              (Unreachable ())
              (pure (walkparams)))))


def CollectPhysicalAddress (_ : Unit) : SailM Bool := do
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 1626) 2) ) : SailM (BitVec 2) )
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 1627) ()) ) : SailM SecurityState )
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
      let (tup__0, tup__1) := (w__1 : (SecurityState × (BitVec 2)))
      let owning_ss : SecurityState := tup__0
      let owning_el : (BitVec 2) := tup__1
      let w__4 ← (( do
        if (((HaveEL EL2) : Bool) : Bool)
        then
          (do
            if (((bne owning_ss SS_Secure) : Bool) : Bool)
            then (pure true)
            else
              (do
                (IsSecureEL2Enabled ())))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          if ((← do
               let w__5 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_PMSCR_EL2_Type_PA w__5) == 1#1) : Bool)))) : Bool)
          then
            (do
              if (((owning_el == EL2) : Bool) : Bool)
              then (pure true)
              else
                (do
                  let w__6 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_PMSCR_EL1_Type_PA w__6) == 1#1) : Bool)))))
          else (pure false))
      else
        (do
          let w__9 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_PMSCR_EL1_Type_PA w__9) == 1#1)))))


def SPESetDataVirtualAddress (vaddress : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let tbi ← (( do (EffectiveTBI vaddress false w__0.EL) ) : SailM (BitVec 1) )
  let non_tbi_is_zeros ← (( do (__IMPDEF_boolean "SPE non-tbi tag is zero") ) : SailM Bool )
  if (((tbi == 1#1) || (! non_tbi_is_zeros)) : Bool)
  then
    (do
      let w__1 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      let w__2 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      writeReg SPESampleAddress (vectorUpdate w__1 SPEAddrPosDataVirtual
        (Sail.BitVec.updateSubrange (GetElem?.getElem! w__2 SPEAddrPosDataVirtual) 63 0
          (Sail.BitVec.extractLsb vaddress 63 0))))
  else
    (do
      let w__3 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      let w__4 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      writeReg SPESampleAddress (vectorUpdate w__3 SPEAddrPosDataVirtual
        (Sail.BitVec.updateSubrange (GetElem?.getElem! w__4 SPEAddrPosDataVirtual) 63 56
          (Zeros (n := 8))))
      let w__5 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      let w__6 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      writeReg SPESampleAddress (vectorUpdate w__5 SPEAddrPosDataVirtual
        (Sail.BitVec.updateSubrange (GetElem?.getElem! w__6 SPEAddrPosDataVirtual) 55 0
          (Sail.BitVec.extractLsb vaddress 55 0))))
  let w__7 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
  writeReg SPESampleAddressValid (vectorUpdate w__7 SPEAddrPosDataVirtual true)


def ProtectionEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  ArmFull.assert (HaveEL el) "sail-arm/v8_base.sail:28475.21-28475.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailME Bool (BitVec 2) )
  let w__0 ← (( do (ELUsingAArch32 regime) ) : SailME Bool Bool )
  ArmFull.assert (! w__0) "sail-arm/v8_base.sail:28477.43-28477.44"
  let w__1 ← (( do (IsD128Enabled el) ) : SailME Bool Bool )
  if ((! w__1) : Bool)
  then
    (do
      let questionMark := regime
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            if ((← do
                 (IsTCR2EL1Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg TCR2_EL1 ) : SailME Bool (BitVec 64) )
                (pure ((((_get_TCR2_EL1_Type_PnCH w__3) == 1#1) : Bool))))
            else (pure false) ) : SailME Bool Bool )
          SailME.throw (w__4 : Bool))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__7 ← (( do
                if ((← do
                     (IsTCR2EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg TCR2_EL2 ) : SailME Bool (BitVec 64) )
                    (pure ((((_get_TCR2_EL2_Type_PnCH w__6) == 1#1) : Bool))))
                else (pure false) ) : SailME Bool Bool )
              SailME.throw (w__7 : Bool))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__8 ← (( do readReg TCR_EL3 ) : SailME Bool (BitVec 64) )
                  SailME.throw (((_get_TCR_EL3_Type_PnCH w__8) == 1#1) : Bool))
              else (pure (()))))
      (pure (false)))
  else (pure (true))


/-- Type quantifiers: index : Int, width : Nat, width ≥ 0 -/
def ZAvector_read (index : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  ArmFull.assert (width == SVL) "sail-arm/v8_base.sail:31134.23-31134.24"
  ArmFull.assert ((index ≥b 0) && (index <b (Int.ediv width 8))) "sail-arm/v8_base.sail:31135.45-31135.46"
  let w__0 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
      (GetElem?.getElem! w__0 (Sail.Int.toNatChecked (index)))
      (Sail.Int.toNatChecked ((width -i 1))) 0))))


/-- Type quantifiers: index : Int, width : Nat, width ≥ 0 -/
def ZAvector_set (index : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  ArmFull.assert (width == SVL) "sail-arm/v8_base.sail:31144.23-31144.24"
  ArmFull.assert ((index ≥b 0) && (index <b (Int.ediv width 8))) "sail-arm/v8_base.sail:31145.45-31145.46"
  let w__0 ← (( do (ConstrainUnpredictableBool Unpredictable_SMEZEROUPPER) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
      writeReg _ZA (vectorUpdate w__1 (Sail.Int.toNatChecked (index))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.zeroExtend value_name MAX_VL))))
  else
    (do
      let w__2 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
      let w__3 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
      writeReg _ZA (vectorUpdate w__2 (Sail.Int.toNatChecked (index))
        (Sail.BitVec.castWidth (m := 2048) (Sail.BitVec.updateSubrange
          (GetElem?.getElem! w__3 (Sail.Int.toNatChecked (index)))
          (Sail.Int.toNatChecked ((width -i 1))) 0 (Sail.BitVec.castWidth value_name)))))


def AArch32_PhysicalSErrorSyndrome (_ : Unit) : SailM (BitVec 16) := do
  let syndrome : (BitVec 32) := (Zeros (n := 32))
  let fault ← (( do (GetPendingPhysicalSError ()) ) : SailM FaultRecord )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let syndrome ← (( do
    if ((w__0.EL == EL2) : Bool)
    then
      (do
        let errstate ← (( do (AArch32_PEErrorState fault) ) : SailM ErrorState )
        let w__1 ← (( do (AArch32_EncodeAsyncErrorSyndrome errstate) ) : SailM (BitVec 2) )
        let syndrome := ((Sail.BitVec.updateSubrange syndrome 11 10 w__1) : (BitVec 32))
        let syndrome : (BitVec 32) := (BitVec.update syndrome 9 (Bit fault.extflag))
        let syndrome : (BitVec 32) := (Sail.BitVec.updateSubrange syndrome 5 0 0b010001#6)
        (pure (syndrome)))
    else
      (do
        let w__2 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let long_format : Bool := ((_get_TTBCR_Type_EAE w__2) == 1#1)
        (AArch32_CommonFaultStatus fault long_format)) ) : SailM (BitVec 32) )
  (pure ((Sail.BitVec.extractLsb syndrome 15 0)))


def AArch64_vESBOperation (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
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
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:33362.63-33362.64"
  let vSEI_enabled ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_AMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let vSEI_pending ← (( do
    if (vSEI_enabled : Bool)
    then
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_VSE w__7) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let vintdis ← (( do
    if ((← do
         (Halted ())) : Bool)
    then (pure true)
    else
      (do
        (ExternalDebugInterruptsDisabled EL1)) ) : SailM Bool )
  let vmasked ← (( do
    if (vintdis : Bool)
    then (pure true)
    else
      (do
        let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__10.A == 1#1) : Bool)))) ) : SailM Bool )
  if ((vSEI_pending && vmasked) : Bool)
  then
    (do
      let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let target : (BitVec 32) := (Zeros (n := 32))
          let target : (BitVec 32) := (BitVec.update target 31 (Bit 1#1))
          let w__12 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
          let target :=
            ((Sail.BitVec.updateSubrange target 15 14 (Sail.BitVec.extractLsb w__12 15 14)) : (BitVec 32))
          let w__13 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
          let target :=
            ((BitVec.update target 12
              (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__13 12)])))) : (BitVec 32))
          let w__14 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
          let target := ((BitVec.update target 9 (Bit (_get_TTBCR_Type_EAE w__14))) : (BitVec 32))
          let w__15 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
          let target : (BitVec 32) :=
            if (((_get_TTBCR_Type_EAE w__15) == 1#1) : Bool)
            then (Sail.BitVec.updateSubrange target 5 0 0b010001#6)
            else
              (let target : (BitVec 32) :=
                (Sail.BitVec.updateSubrange target 10 10 (Sail.BitVec.extractLsb 0b10110#5 4 4))
              (Sail.BitVec.updateSubrange target 3 0 (Sail.BitVec.extractLsb 0b10110#5 3 0)))
          (VDISR_write (Mk_VDISR_Type target)))
      else
        (do
          let target : (BitVec 64) := (Zeros (n := 64))
          let target : (BitVec 64) := (BitVec.update target 31 (Bit 1#1))
          let w__16 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
          let target :=
            ((Sail.BitVec.updateSubrange target 24 0 (Sail.BitVec.extractLsb w__16 24 0)) : (BitVec 64))
          writeReg VDISR_EL2 (Mk_VDISR_EL2_Type target))
      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__17 8 8 0#1))
  else (pure (()))


end ArmFull.Functions
