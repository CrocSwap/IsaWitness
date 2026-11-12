import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0050
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0098
import ArmFull.Fn.M0100
import ArmFull.Fn.M0117
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0149
import ArmFull.Fn.M0150

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

def AArch32_TLBContextEL2 (va : (BitVec 32)) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2532) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := SS_NonSecure }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL2 }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend va 64) }
  let tlbcontext : TLBContext := { tlbcontext with tg := TGx_4KB }
  let w__0 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
        (pure ((_get_HTTBR_Type_CnP w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let tlbcontext := ({ tlbcontext with cnp := w__2 } : TLBContext)
  (pure (tlbcontext))


def AArch32_IPAIsOutOfRange (walkparams : S2TTWParams) (ipa : (BitVec 40)) : Bool :=
  let iasize : Int := (AArch32_S2IASize walkparams.t0sz)
  ((iasize <b 40) && (! (is_zero_subrange ipa 39 iasize)))


def AArch32_S2HasPermissionsFault (walkparams : S2TTWParams) (perms : Permissions) (memtype : MemType) (accdesc : AccessDescriptor) : SailM Bool := do
  let constraint_name ← (( do (undefined_Constraint (← occLabel 2537) ()) ) : SailM Constraint )
  let px ← (( do (undefined_bitvector_at (← occLabel 2538) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 2539) 1) ) : SailM (BitVec 1) )
  let r : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access perms.s2ap 0)]))
  let w : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access perms.s2ap 1)]))
  let x ← (( do (undefined_bitvector_at (← occLabel 2540) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do (HaveExtendedExecuteNeverExt ()) ) : SailM Bool )
  let x : (BitVec 1) :=
    if (w__0 : Bool)
    then
      (let (px, ux) : ((BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 2 (perms.s2xn +++ perms.s2xnx)) with
        | 0b00 =>
          (let (tup__0, tup__1) := ((r, r) : ((BitVec 1) × (BitVec 1)))
          let px : (BitVec 1) := tup__0
          let ux : (BitVec 1) := tup__1
          (px, ux))
        | 0b01 =>
          (let (tup__0, tup__1) := ((0#1, r) : ((BitVec 1) × (BitVec 1)))
          let px : (BitVec 1) := tup__0
          let ux : (BitVec 1) := tup__1
          (px, ux))
        | 0b10 =>
          (let (tup__0, tup__1) := ((0#1, 0#1) : ((BitVec 1) × (BitVec 1)))
          let px : (BitVec 1) := tup__0
          let ux : (BitVec 1) := tup__1
          (px, ux))
        | _ =>
          (let (tup__0, tup__1) := ((r, 0#1) : ((BitVec 1) × (BitVec 1)))
          let px : (BitVec 1) := tup__0
          let ux : (BitVec 1) := tup__1
          (px, ux))
      if ((accdesc.el == EL0) : Bool)
      then ux
      else px)
    else (r &&& (Complement.complement perms.s2xn))
  if ((BEq.beq accdesc.acctype AccessType_TTW) : Bool)
  then (pure ((((walkparams.ptw == 1#1) && (BEq.beq memtype MemType_Device)) || (r == 0#1))))
  else
    (do
      if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
      then
        (do
          let constraint_name ← (( do (ConstrainUnpredictable Unpredictable_INSTRDEVICE) ) : SailM
            Constraint )
          (pure ((((BEq.beq constraint_name Constraint_FAULT) && (BEq.beq memtype MemType_Device)) || (x == 0#1)))))
      else
        (pure (if (((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq accdesc.acctype
                 AccessType_DC)) : Bool)
          then false
          else
            (if (accdesc.write : Bool)
            then (w == 0#1)
            else (r == 0#1)))))


def AArch32_GetS2TLBContext (ipa : FullAddress) : SailM TLBContext := do
  ArmFull.assert (BEq.beq ipa.paspace PAS_NonSecure) "sail-arm/v8_base.sail:37808.39-37808.40"
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2541) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := SS_NonSecure }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL10 }
  let tlbcontext : TLBContext := { tlbcontext with ipaspace := ipa.paspace }
  let w__0 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
  let tlbcontext :=
    ({ tlbcontext with vmid := (Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__0) 16) } : TLBContext)
  let tlbcontext : TLBContext := { tlbcontext with tg := TGx_4KB }
  let tlbcontext : TLBContext := { tlbcontext with includes_s1_name := false }
  let tlbcontext : TLBContext := { tlbcontext with includes_s2_name := true }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend ipa.address 64) }
  let w__1 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let w__3 ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
        (pure ((_get_VTTBR_Type_CnP w__2))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let tlbcontext := ({ tlbcontext with cnp := w__3 } : TLBContext)
  (pure (tlbcontext))


def AArch32_VAIsOutOfRange (regime : Regime) (walkparams : S1TTWParams) (va : (BitVec 32)) : SailM Bool := do
  let iasize ← (( do (undefined_int_at (← occLabel 2573) ()) ) : SailM Int )
  let lo_iasize ← (( do (undefined_int_at (← occLabel 2574) ()) ) : SailM Int )
  let up_iasize ← (( do (undefined_int_at (← occLabel 2575) ()) ) : SailM Int )
  (pure (if ((BEq.beq regime Regime_EL2) : Bool)
    then
      (let iasize : Int := (AArch32_S1IASize walkparams.t0sz)
      ((walkparams.t0sz != 0b000#3) && (! (is_zero_subrange va 31 iasize))))
    else
      (if (((walkparams.t1sz != 0b000#3) && (walkparams.t0sz != 0b000#3)) : Bool)
      then
        (let lo_iasize : Int := (AArch32_S1IASize walkparams.t0sz)
        let up_iasize : Int := (AArch32_S1IASize walkparams.t1sz)
        ((! (is_zero_subrange va 31 lo_iasize)) && (! (is_ones_subrange va 31 up_iasize))))
      else false)))


def __IMPDEF_MemoryAttributes (x : String) : SailM MemoryAttributes := do
  (__UNKNOWN_MemoryAttributes ())


def CheckOSUnlockCatch (_ : Unit) : SailM Unit := do
  let w__6 ← (( do
    if ((← do
         if ((← do
              (HaveDoPD ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg CTIDEVCTL ) : SailM (BitVec 32) )
             (pure ((((_get_CTIDEVCTL_Type_OSUCE w__1) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__3 ← (( do (HaveDoPD ()) ) : SailM Bool )
             (pure (((! w__3) : Bool)))) : Bool)
        then
          (do
            let w__4 ← (( do readReg EDECR ) : SailM (BitVec 32) )
            (pure ((((_get_EDECR_Type_OSUCE w__4) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do (Halted ()) ) : SailM Bool )
      if ((! w__7) : Bool)
      then
        (do
          let w__8 ← (( do readReg EDESR ) : SailM (BitVec 32) )
          writeReg EDESR (Sail.BitVec.updateSubrange w__8 0 0 1#1))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV84 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap4_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV83 enabled))
  else (pure (()))


/-- Type quantifiers: value_name : Int -/
def decode_max_sveveclen (value_name : Int) : SailM Int := do
  let max_vl : Int := (value_name *i 64)
  let max_vl : Int :=
    if ((max_vl >b 2048) : Bool)
    then 2048
    else max_vl
  let max_vl : Int := max_vl
  let w__0 ← (( do (IsPow2 max_vl) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (FloorPow2 max_vl))
  else (pure (max_vl))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AArch32_WatchpointByteMatch (n : Nat) (vaddress : (BitVec 32)) : SailM Bool := SailME.run do
  let LSB ← (( do (undefined_bitvector_at (← occLabel 2672) 8) ) : SailME Bool (BitVec 8) )
  let MSB ← (( do (undefined_bitvector_at (← occLabel 2673) 8) ) : SailME Bool (BitVec 8) )
  let top : Nat := 31
  let w__0 ← (( do (DBGWVR_read n) ) : SailME Bool (BitVec 32) )
  let bottom : Nat :=
    (Sail.Int.toNatChecked (if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 2)])) == 1#1) : Bool)
    then 2
    else 3))
  let bottom : Int := bottom
  let w__1 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
  let byte_select_match : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (_get_DBGWCR_Type_BAS w__1)
          (BitVec.toNat (Sail.BitVec.extractLsb vaddress (Sail.Int.toNatChecked ((bottom -i 1))) 0)))])) != 0#1)
  let w__2 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
  let mask : Int := (BitVec.toNat (_get_DBGWCR_Type_MASK w__2))
  let w__4 ← (( do
    if (((mask >b 0) : Bool) : Bool)
    then
      (do
        let w__3 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
        (pure (((! (IsOnes (_get_DBGWCR_Type_BAS w__3))) : Bool))))
    else (pure false) ) : SailME Bool Bool )
  let (bottom, byte_select_match) ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (ConstrainUnpredictableBool Unpredictable_WPMASKANDBAS) ) : SailME Bool
          Bool )
        let byte_select_match := (w__5 : Bool)
        (pure ((bottom, byte_select_match))))
    else
      (do
        let w__6 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
        let w__7 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
        let LSB : (BitVec 8) :=
          ((_get_DBGWCR_Type_BAS w__6) &&& (Complement.complement
              (BitVec.subInt (_get_DBGWCR_Type_BAS w__7) 1)))
        let w__8 ← (( do (DBGWCR_read n) ) : SailME Bool (BitVec 32) )
        let MSB : (BitVec 8) := ((_get_DBGWCR_Type_BAS w__8) + LSB)
        if ((! (IsZero (MSB &&& (BitVec.subInt MSB 1)))) : Bool)
        then
          (do
            let w__9 ← (( do (ConstrainUnpredictableBool Unpredictable_WPBASCONTIGUOUS) ) : SailME
              Bool Bool )
            let byte_select_match := (w__9 : Bool)
            let bottom : Nat := 3
            (pure ((bottom, byte_select_match))))
        else (pure ((bottom, byte_select_match)))) ) : SailME Bool (Int × Bool) )
  let bottom : Int := bottom
  let mask ← (( do
    if (((mask >b 0) && (mask ≤b 2)) : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 2674) ()) ) : SailME Bool Constraint )
        let w__10 ← (( do (ConstrainUnpredictableInteger 3 31 Unpredictable_RESWPMASK) ) : SailME
          Bool (Constraint × Int) )
        let (tup__0, tup__1) := (w__10 : (Constraint × Int))
        let c : Constraint := tup__0
        let mask : Int := tup__1
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
              c Constraint_UNKNOWN))) "sail-arm/v8_base.sail:40692.88-40692.89"
        match c with
        | .Constraint_DISABLED =>
          (do
            SailME.throw (false : Bool)
            (pure (mask)))
        | .Constraint_NONE => (pure (0))
        | _ => (pure (mask)))
    else (pure (mask)) ) : SailME Bool Int )
  let mask : Int := mask
  let WVR_match ← (( do (undefined_bool_at (← occLabel 2675) ()) ) : SailME Bool Bool )
  let WVR_match ← (( do
    if ((mask >b bottom) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b mask) && ((mask ≤b top) && (top <b 32))) "sail-arm/v8_base.sail:40706.67-40706.68"
        let w__11 ← (( do (DBGWVR_read n) ) : SailME Bool (BitVec 32) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (mask : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress top (Sail.Int.toNatChecked (mask)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              w__11 top (Sail.Int.toNatChecked (mask))))) : Bool)
        let w__13 ← (( do
          if ((WVR_match : Bool) : Bool)
          then
            (do
              let w__12 ← (( do (DBGWVR_read n) ) : SailME Bool (BitVec 32) )
              (pure (((! (is_zero_subrange w__12 (mask -i 1) bottom)) : Bool))))
          else (pure false) ) : SailME Bool Bool )
        if (w__13 : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_WPMASKEDBITS))
        else (pure (WVR_match)))
    else
      (do
        let w__15 ← (( do (DBGWVR_read n) ) : SailME Bool (BitVec 32) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (bottom : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress top (Sail.Int.toNatChecked (bottom)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              w__15 top (Sail.Int.toNatChecked (bottom))))) : Bool)
        (pure (WVR_match))) ) : SailME Bool Bool )
  (pure ((WVR_match && byte_select_match)))


def A32ExpandImm_C (imm12 : (BitVec 12)) (carry_in : (BitVec 1)) : SailM ((BitVec 32) × (BitVec 1)) := do
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 2697) 1) ) : SailM (BitVec 1) )
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2698) 32) ) : SailM (BitVec 32) )
  let unrotated_value : (BitVec 32) :=
    (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb imm12 7 0) 32)
  let w__0 ← (( do
    (Shift_C unrotated_value SRType_ROR (2 *i (BitVec.toNat (Sail.BitVec.extractLsb imm12 11 8)))
      carry_in) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__0 : ((BitVec 32) × (BitVec 1)))
  let imm32 : (BitVec 32) := tup__0
  let carry_out : (BitVec 1) := tup__1
  (pure ((imm32, carry_out)))


/-- Type quantifiers: k_N : Nat, amount : Int, k_N ≥ 0 -/
def Shift (value_name : (BitVec k_N)) (srtype : SRType) (amount : Int) (carry_in : (BitVec 1)) : SailM (BitVec k_N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2703)
      (Sail.BitVec.length value_name))) ) : SailM (BitVec k_N) )
  let (__tup_0, _) ← (( do (Shift_C value_name srtype amount carry_in) ) : SailM
    ((BitVec k_N) × (BitVec 1)) )
  (pure ((Sail.BitVec.castWidth __tup_0)))


/-- Type quantifiers: N : Nat, i : Int, k_is_unsigned : Bool, N ≥ 0 -/
def Sat (i : Int) (N : Nat) (is_unsigned : Bool) : SailM (BitVec N) := do
  if (is_unsigned : Bool)
  then
    (do
      ArmFull.assert (0 ≤b (N -i 1)) "sail-arm/v8_base.sail:42744.38-42744.39"
      ((Sail.BitVec.castWidth ) <$> (UnsignedSat i N)))
  else
    (do
      ArmFull.assert (0 ≤b (N -i 1)) "sail-arm/v8_base.sail:42747.38-42747.39"
      ((Sail.BitVec.castWidth ) <$> (SignedSat i N)))


def __set_MPAM1_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  let w__0 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 54 w__0 0 (BitVec.slice r 0 54))))
  let w__1 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 5 w__1 55 (BitVec.slice r 55 5))))
  let w__2 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 2 w__2 61 (BitVec.slice r 61 2))))
  if (((! (HaveEL EL3)) && (! (HaveEL EL2))) : Bool)
  then
    (do
      let w__3 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
      (MPAM1_EL1_write (_update_MPAM1_EL1_Type_MPAMEN w__3 (_get_MPAM1_EL1_Type_MPAMEN r))))
  else (pure (()))


def __set_DBGDSCRext (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDSCRext_Type := value_name
  let w__0 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 6 w__0 0 (BitVec.slice r 0 6))))
  let w__1 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 7 w__1 7 (BitVec.slice r 7 7))))
  let w__2 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__2 15 (BitVec.slice r 15 1))))
  let w__3 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__3 20 (BitVec.slice r 20 1))))
  let w__4 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 2 w__4 24 (BitVec.slice r 24 2))))
  let w__5 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__5 28 (BitVec.slice r 28 1))))
  let w__6 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__6) == 1#1) : Bool)
  then
    (do
      let w__7 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TFO w__7 (_get_DBGDSCRext_Type_TFO r))))
  else (pure (()))
  let w__8 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__8) == 1#1) : Bool)
  then
    (do
      let w__9 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull w__9 (_get_DBGDSCRext_Type_RXfull r))))
  else (pure (()))
  let w__10 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__10) == 1#1) : Bool)
  then
    (do
      let w__11 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull w__11 (_get_DBGDSCRext_Type_TXfull r))))
  else (pure (()))
  let w__12 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__12) == 1#1) : Bool)
  then
    (do
      let w__13 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_RXO w__13 (_get_DBGDSCRext_Type_RXO r))))
  else (pure (()))
  let w__14 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__14) == 1#1) : Bool)
  then
    (do
      let w__15 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXU w__15 (_get_DBGDSCRext_Type_TXU r))))
  else (pure (()))
  let w__16 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__16) == 1#1) : Bool)
  then
    (do
      let w__17 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_INTdis w__17 (_get_DBGDSCRext_Type_INTdis r))))
  else (pure (()))
  let w__18 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__18) == 1#1) : Bool)
  then
    (do
      let w__19 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TDA w__19 (_get_DBGDSCRext_Type_TDA r))))
  else (pure (()))
  let w__20 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__20) == 1#1) : Bool)
  then
    (do
      let w__21 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_SC2 w__21 (_get_DBGDSCRext_Type_SC2 r))))
  else (pure (()))
  let w__22 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__22) == 1#1) : Bool)
  then
    (do
      let w__23 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_HDE w__23 (_get_DBGDSCRext_Type_HDE r))))
  else (pure (()))
  let w__24 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  if (((_get_DBGOSLSR_Type_OSLK w__24) == 1#1) : Bool)
  then
    (do
      let w__25 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_ERR w__25 (_get_DBGDSCRext_Type_ERR r))))
  else (pure (()))


/-- Type quantifiers: t : Int -/
def ACTLR_EL3_SysRegRead_c20b5bca7bc57751 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg ACTLR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AFSR0_EL3_SysRegRead_2d1994fbdbde12d8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg AFSR0_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AFSR1_EL3_SysRegRead_bbfc01f9fd46f6c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg AFSR1_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ALLINT_SysRegRead_ee53c92ec04c7280 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          (X_set t 64 (((Zeros (n := 50)) +++ w__1.ALLINT) +++ (Zeros (n := 13)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 50)) +++ w__2.ALLINT) +++ (Zeros (n := 13)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64 (((Zeros (n := 50)) +++ w__3.ALLINT) +++ (Zeros (n := 13)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMAIR2_EL3_SysRegRead_3e5d4dd4506a8fae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg AMAIR2_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMAIR_EL3_SysRegRead_098fd5c15cd15cd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg AMAIR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegRead_c39dc9ffb55dc488 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
          (X_set t 64 (__get_CNTKCTL_EL1 w__2)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHCTL_EL2 w__3)))
              else
                (do
                  let w__4 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTKCTL_EL1 w__4))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTKCTL_EL1 w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPTR_EL3_SysRegRead_7b3995450955fa38 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CPTR_EL3 w__1)))
              else (pure (())))))


end ArmFull.Functions
