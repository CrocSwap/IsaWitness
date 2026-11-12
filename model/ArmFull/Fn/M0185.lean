import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182

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

def IsTCR2EL2Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatTCR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_TCR2En w__1) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then (pure (false))
      else
        (do
          (EL2Enabled ())))


def SelfHostedExtendedBPWPEnabled (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
         (pure (((w__0 ≤b 16) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
        (pure (((w__1 ≤b 16) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let w__8 ← (( do
        if ((← do
             if (((HaveEL EL3) : Bool) : Bool)
             then
               (do
                 let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_MDCR_EL3_Type_EBWE w__3) == 0#1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_EBWE w__6) == 0#1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__8 : Bool)
      then (pure (false))
      else
        (do
          let w__9 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_MDSCR_EL1_Type_EMBWE w__9) == 1#1)))))


/-- Type quantifiers: k_isbreakpnt : Bool -/
def CheckValidStateMatch (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (isbreakpnt : Bool) : SailM (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) := SailME.run do
  let w__0 ← (( do (HaveRME ()) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  if ((! w__0) : Bool)
  then
    (do
      ArmFull.assert (ssce_in == 0#1) "armcert/armcert_c27b.sail:442.29-442.30")
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
            let w__1 ← (( do (HaveSecureState ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
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
          (pure (reserved)))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
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
              let w__2 ← (( do (HaveAArch64 ()) ) : SailME
                (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
              (pure (((! w__2) : Bool))))) && ((((hmc +++ ssc) +++ pxc) == 0b11000#5) : Bool))) ) :
    SailME (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
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
          let w__5 ← (( do (HaveSecureEL2Ext ()) ) : SailME
            (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
          (pure (((! w__5) : Bool)))) && (match (BitVec.setWidth 5 ((hmc +++ ssc) +++ pxc)) with
        | 0b01100 => true
        | 0b10100 => true
        | b__4 =>
          (if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__4 3 2)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   b__4 0 0)) == (1#1 : (BitVec 1)))) : Bool)
          then true
          else false) : Bool))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__6 : Bool)
    then true
    else reserved
  let (hmc, pxc, ssc, ssce) ← (( do
    if (reserved : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 1380) ()) ) : SailME
          (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Constraint )
        let w__7 ← (( do (C27bConstrainControl isbreakpnt) ) : SailME
          (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))
          (Constraint × (BitVec 6)) )
        let (tup__0, tup__1) := (w__7 : (Constraint × (BitVec 6)))
        let c : Constraint := tup__0
        let hmc : (BitVec 1) := (Sail.BitVec.extractLsb tup__1 5 5)
        let ssc : (BitVec 2) := (Sail.BitVec.extractLsb tup__1 4 3)
        let ssce : (BitVec 1) := (Sail.BitVec.extractLsb tup__1 2 2)
        let pxc : (BitVec 2) := (Sail.BitVec.extractLsb tup__1 1 0)
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "armcert/armcert_c27b.sail:498.65-498.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            let w__8 ← (( do (__UNKNOWN_bits 2) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 2) )
            let w__9 ← (( do (__UNKNOWN_bit ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 1) )
            let w__10 ← (( do (__UNKNOWN_bit ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 1) )
            let w__11 ← (( do (__UNKNOWN_bits 2) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 2) )
            SailME.throw ((c, w__8, w__9, w__10, w__11) : (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))))
        else (pure (()))
        (pure ((hmc, pxc, ssc, ssce))))
    else (pure ((hmc, pxc, ssc, ssce))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))
    ((BitVec 1) × (BitVec 2) × (BitVec 2) × (BitVec 1)) )
  (pure ((Constraint_NONE, ssc, ssce, hmc, pxc)))


/-- Type quantifiers: n : Int -/
def IsContextMatchingBreakpoint (n : Int) : SailM Bool := do
  let lower ← (( do (undefined_int_at (← occLabel 1381) ()) ) : SailM Int )
  let upper ← (( do (undefined_int_at (← occLabel 1382) ()) ) : SailM Int )
  let w__0 ← (( do (ContextMatchingBreakpointRange ()) ) : SailM (Int × Int) )
  let (tup__0, tup__1) := (w__0 : (Int × Int))
  let lower : Int := tup__0
  let upper : Int := tup__1
  let upper : Int := upper
  let lower : Int := lower
  (pure (((n ≥b lower) && (n ≤b upper))))


def AArch64_S1Enabled (regime : Regime) (acctype : AccessType) : SailM Bool := do
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL3_Type_M w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_M w__1) == 1#1))))
  | .Regime_EL20 =>
    (do
      let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_M w__2) == 1#1))))
  | .Regime_EL10 =>
    (do
      if ((← do
           if ((← do
                let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
                (pure (((! w__3) : Bool)))) : Bool)
           then (pure true)
           else
             (do
               let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure (((((_get_HCR_EL2_Type_DC w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b00#2) : Bool))))) : Bool)
      then
        (do
          let w__7 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_SCTLR_EL1_Type_M w__7) == 1#1) : Bool))))
      else (pure false))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 1465) ()))


/-- Type quantifiers: k_N : Nat, level : Int, 0 < k_N -/
def AArch64_DecodeDescriptorType (descriptor : (BitVec k_N)) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (level : Int) : SailM DescriptorType := do
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 0)])) == 0#1) : Bool)
  then (pure (DescriptorType_Invalid))
  else
    (do
      if ((d128 == 1#1) : Bool)
      then
        (do
          ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:24904.35-24904.36"
          let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
          (pure (if ((((BEq.beq tgx TGx_16KB) || (BEq.beq tgx TGx_64KB)) && (((BitVec.toNat skl) == 3) : Bool)) : Bool)
            then DescriptorType_Invalid
            else
              (let effective_level : Int := (level +i (BitVec.toNat skl))
              if ((effective_level >b FINAL_LEVEL) : Bool)
              then DescriptorType_Invalid
              else
                (if ((effective_level == FINAL_LEVEL) : Bool)
                then DescriptorType_Leaf
                else DescriptorType_Table)))))
      else
        (do
          ArmFull.assert (1 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:24918.33-24918.34"
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 1)])) == 1#1) : Bool)
          then
            (pure (if ((level == FINAL_LEVEL) : Bool)
              then DescriptorType_Leaf
              else DescriptorType_Table))
          else
            (do
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 1)])) == 0#1) : Bool)
              then
                (do
                  let w__0 ← (( do (AArch64_BlockDescSupported d128 ds tgx level) ) : SailM Bool )
                  let w__1 : DescriptorType :=
                    if (w__0 : Bool)
                    then DescriptorType_Leaf
                    else DescriptorType_Invalid
                  (pure (w__1)))
              else
                (do
                  (undefined_DescriptorType (← occLabel 1471) ())))))


def VMID_read (_ : Unit) : SailM (BitVec 16) := do
  let w__0 ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          let w__4 ← (( do
            if ((← do
                 (Have16bitVMID ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_VTCR_EL2_Type_VS w__3) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_VTTBR_EL2_Type_VMID w__5))))
          else
            (do
              let w__6 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((Sail.BitVec.zeroExtend
                  (Sail.BitVec.extractLsb (_get_VTTBR_EL2_Type_VMID w__6) 7 0) 16)))))
      else
        (do
          let w__8 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
          (pure ((Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__8) 16)))))
  else
    (do
      let w__11 ← (( do
        if (((HaveEL EL2) : Bool) : Bool)
        then
          (do
            (HaveSecureEL2Ext ()))
        else (pure false) ) : SailM Bool )
      let w__12 : (BitVec 16) :=
        if (w__11 : Bool)
        then (Zeros (n := 16))
        else VMID_NONE
      (pure (w__12)))


def AArch64_OAOutOfRange (address : (BitVec 56)) (d128 : (BitVec 1)) (ps : (BitVec 3)) (tgx : TGx) : SailM Bool := do
  let oasize ← (( do (AArch64_PhysicalAddressSize d128 ps tgx) ) : SailM Int )
  (pure (if ((oasize <b 56) : Bool)
    then (! (is_zero_subrange address 55 oasize))
    else false))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S1ApplyTablePerms (permissions_in : Permissions) (descriptor : (BitVec k_N)) (regime : Regime) (walkparams : S1TTWParams) : SailM Permissions := do
  let permissions : Permissions := permissions_in
  let ap_table ← (( do (undefined_bitvector_at (← occLabel 1493) 2) ) : SailM (BitVec 2) )
  let pxn_table ← (( do (undefined_bitvector_at (← occLabel 1494) 1) ) : SailM (BitVec 1) )
  let uxn_table ← (( do (undefined_bitvector_at (← occLabel 1495) 1) ) : SailM (BitVec 1) )
  let xn_table ← (( do (undefined_bitvector_at (← occLabel 1496) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do
    (pure ((← do
          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false)) && ((walkparams.nv1 == 1#1) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let (ap_table, pxn_table) ← (( do
        if ((walkparams.d128 == 1#1) : Bool)
        then
          (do
            ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25581.39-25581.40"
            let ap_table : (BitVec 2) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 126)])) +++ 0#1)
            let pxn_table : (BitVec 1) :=
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
            (pure ((ap_table, pxn_table))))
        else
          (do
            ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25585.38-25585.39"
            let ap_table : (BitVec 2) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 62)])) +++ 0#1)
            let pxn_table : (BitVec 1) :=
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
            (pure ((ap_table, pxn_table)))) ) : SailM ((BitVec 2) × (BitVec 1)) )
      let permissions : Permissions :=
        { permissions with ap_table := (permissions.ap_table ||| ap_table) }
      let permissions : Permissions :=
        { permissions with pxn_table := (permissions.pxn_table ||| pxn_table) }
      (pure (permissions)))
  else
    (do
      if ((HasUnprivileged regime) : Bool)
      then
        (do
          let (ap_table, pxn_table, uxn_table) ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25593.39-25593.40"
                let ap_table : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 126 125)
                let uxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
                let pxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 123)]))
                (pure ((ap_table, pxn_table, uxn_table))))
            else
              (do
                ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25598.38-25598.39"
                let ap_table : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 62 61)
                let uxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
                let pxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 59)]))
                (pure ((ap_table, pxn_table, uxn_table)))) ) : SailM
            ((BitVec 2) × (BitVec 1) × (BitVec 1)) )
          let permissions : Permissions :=
            { permissions with ap_table := (permissions.ap_table ||| ap_table) }
          let permissions : Permissions :=
            { permissions with uxn_table := (permissions.uxn_table ||| uxn_table) }
          let permissions : Permissions :=
            { permissions with pxn_table := (permissions.pxn_table ||| pxn_table) }
          (pure (permissions)))
      else
        (do
          let (ap_table, xn_table) ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25608.39-25608.40"
                let ap_table : (BitVec 2) :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 126)])) +++ 0#1)
                let xn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
                (pure ((ap_table, xn_table))))
            else
              (do
                ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25612.38-25612.39"
                let ap_table : (BitVec 2) :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 62)])) +++ 0#1)
                let xn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
                (pure ((ap_table, xn_table)))) ) : SailM ((BitVec 2) × (BitVec 1)) )
          let permissions : Permissions :=
            { permissions with ap_table := (permissions.ap_table ||| ap_table) }
          let permissions : Permissions :=
            { permissions with xn_table := (permissions.xn_table ||| xn_table) }
          (pure (permissions))))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_S2TxSZFaults (walkparams : S2TTWParams) (s1aarch64 : Bool) : SailM Bool := do
  let mintxsz ← (( do (AArch64_S2MinTxSZ walkparams.d128 walkparams.ds walkparams.tgx s1aarch64) )
    : SailM Int )
  let maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailM Int )
  if (((BitVec.toNat walkparams.txsz) <b mintxsz) : Bool)
  then
    (do
      if ((← do
           (Have52BitPAExt ())) : Bool)
      then (pure true)
      else
        (do
          (__IMPDEF_boolean "Fault on TxSZ value below minimum")))
  else
    (do
      if (((BitVec.toNat walkparams.txsz) >b maxtxsz) : Bool)
      then
        (do
          (__IMPDEF_boolean "Fault on TxSZ value above maximum"))
      else (pure (false)))


def AArch64_IsUnprivAccessPriv (_ : Unit) : SailM Bool := do
  let privileged ← (( do (undefined_bool_at (← occLabel 1676) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  let privileged ← (( do
    if ((questionMark == EL0) : Bool)
    then (pure (false))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     (HaveNVExt ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV w__4) +++ (_get_HCR_EL2_Type_NV1 w__5)) == 0b11#2) : Bool))))
            else (pure false))
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
                      let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                  else (pure false) ) : SailM Bool )
                let privileged := ((! w__10) : Bool)
                (pure (privileged)))
            else
              (let privileged : Bool :=
                if ((questionMark == EL3) : Bool)
                then true
                else privileged
              (pure (privileged))))) ) : SailM Bool )
  let w__13 ← (( do
    if ((← do
         (HaveUAOExt ())) : Bool)
    then
      (do
        let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__12.UAO == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      let privileged := ((w__14.EL != EL0) : Bool)
      (pure (privileged)))
  else (pure (privileged))


def IsTMEEnabled (_ : Unit) : SailM Bool := SailME.run do
  let w__5 ← (( do
    (pure ((← do
          if ((← do
               let w__0 ← (( do readReg PSTATE ) : SailME Bool ProcState )
               (pure (((w__0.EL == EL0) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              if ((← do
                   let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                   (pure (((w__1.EL == EL1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__2.EL == EL2) : Bool)))))) && ((HaveEL EL3) : Bool))) ) : SailME Bool
    Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg SCR_EL3 ) : SailME Bool (BitVec 64) )
      if (((_get_SCR_EL3_Type_TME w__6) == 0#1) : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  let w__11 ← (( do
    if ((← do
         if ((← do
              let w__7 ← (( do readReg PSTATE ) : SailME Bool ProcState )
              (pure (((w__7.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__8 ← (( do readReg PSTATE ) : SailME Bool ProcState )
             (pure (((w__8.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailME Bool Bool )
  if (w__11 : Bool)
  then
    (do
      let w__12 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
      if (((_get_HCR_EL2_Type_TME w__12) == 0#1) : Bool)
      then
        (do
          SailME.throw (false : Bool))
      else (pure (())))
  else (pure (()))
  (pure (true))


def EffectiveMDSELR_EL1_BANK (_ : Unit) : SailM (BitVec 2) := do
  let num_bp ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let num_wp ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
  if (((num_bp ≤b 16) && (num_wp ≤b 16)) : Bool)
  then (pure (0b00#2))
  else
    (do
      let w__11 ← (( do
        if ((← do
             if ((← do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__0 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_MDCR_EL3_Type_EBWE w__0) == 0#1) : Bool))))
                  else (pure false)) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      if ((← do
                           let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__2.EL != EL3) : Bool)))) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL2_Type_EBWE w__5) == 0#1) : Bool))))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__8.EL == EL1) : Bool)))) : Bool)
            then
              (do
                let w__9 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
                (pure ((((_get_MDSCR_EL1_Type_EMBWE w__9) == 0#1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__11 : Bool)
      then (pure (0b00#2))
      else
        (do
          let w__12 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
          let bank : (BitVec 2) := (_get_MDSELR_EL1_Type_BANK w__12)
          if (((((bank == 0b11#2) && (num_bp ≤b 48)) && (num_wp ≤b 48)) || (((bank == 0b10#2) && (num_bp ≤b 32)) && (num_wp ≤b 32))) : Bool)
          then
            (do
              let maximum : Int :=
                if ((num_bp >b num_wp) : Bool)
                then num_bp
                else num_wp
              let last_bank : Int := (Int.ediv (Sail.Int.toNatChecked ((maximum -i 1))) 16)
              let selected ← (( do
                ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 2421) 0
                  last_bank))) ) : SailM Nat )
              let __tup_1 : (BitVec 2) := (integer_subrange selected 1 0)
              (pure (__tup_1)))
          else (pure (bank))))


end ArmFull.Functions
