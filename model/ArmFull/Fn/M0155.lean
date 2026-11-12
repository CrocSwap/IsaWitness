import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0117
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146

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

def AbovePPS (address : (BitVec 56)) : SailM Bool := do
  let pps ← (( do (DecodePPS ()) ) : SailM Int )
  (pure (if ((pps ≥b 56) : Bool)
    then false
    else (! (is_zero_subrange address 55 pps))))


def GPICheck (paspace : PASpace) (gpi : (BitVec 4)) : SailM Bool := do
  let questionMark := gpi
  if ((questionMark == GPT_NoAccess) : Bool)
  then (pure (false))
  else
    (do
      if ((questionMark == GPT_Secure) : Bool)
      then
        (do
          let w__0 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
          ArmFull.assert w__0 "sail-arm/v8_base.sail:19498.35-19498.36"
          (pure ((BEq.beq paspace PAS_Secure))))
      else
        (do
          if ((questionMark == GPT_NonSecure) : Bool)
          then (pure ((BEq.beq paspace PAS_NonSecure)))
          else
            (do
              if ((questionMark == GPT_Root) : Bool)
              then (pure ((BEq.beq paspace PAS_Root)))
              else
                (do
                  if ((questionMark == GPT_Realm) : Bool)
                  then (pure ((BEq.beq paspace PAS_Realm)))
                  else
                    (do
                      if ((questionMark == GPT_Any) : Bool)
                      then (pure (true))
                      else
                        (do
                          (Unreachable ())
                          (undefined_bool_at (← occLabel 1225) ())))))))


def GPIValid (gpi : (BitVec 4)) : SailM Bool := do
  if ((gpi == GPT_Secure) : Bool)
  then
    (do
      (HaveSecureEL2Ext ()))
  else
    (pure (((gpi == GPT_NoAccess) || ((gpi == GPT_NonSecure) || ((gpi == GPT_Root) || ((gpi == GPT_Realm) || (gpi == GPT_Any)))))))


def GPTTLBLookup (pa : (BitVec 56)) (pgs : PGSe) : SailM GPTTLBLine := do
  (__UNKNOWN_GPTTLBLine ())


def AArch64_MaxTxSZ (tgx : TGx) : SailM Int := do
  let w__0 ← (( do (HaveSmallTranslationTableExt ()) ) : SailM Bool )
  let w__1 : Int :=
    if (w__0 : Bool)
    then
      (match tgx with
      | .TGx_4KB => 48
      | .TGx_16KB => 48
      | .TGx_64KB => 47)
    else 39
  (pure (w__1))


def AArch64_S1MinTxSZ (regime : Regime) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) : SailM Int := do
  let w__1 ← (( do
    (pure ((← do
          (Have56BitVAExt ())) && ((d128 == 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (pure (if ((HasUnprivileged regime) : Bool)
      then 9
      else 8))
  else
    (do
      let w__4 ← (( do
        (pure ((← do
              (pure ((← do
                    (Have52BitVAExt ())) && ((BEq.beq tgx TGx_64KB) : Bool)))) || ((ds == 1#1) : Bool)))
        ) : SailM Bool )
      let w__5 : Int :=
        if (w__4 : Bool)
        then 12
        else 16
      (pure (w__5)))


/-- Type quantifiers: k_isqarma3 : Bool -/
def ComputePACQARMA (data : (BitVec 64)) (modifier : (BitVec 64)) (key0 : (BitVec 64)) (key1 : (BitVec 64)) (isqarma3 : Bool) : SailM (BitVec 64) := do
  let roundkey ← (( do (undefined_bitvector_at (← occLabel 1290) 64) ) : SailM (BitVec 64) )
  let Alpha : (BitVec 64) := 0xC0AC29B7C97C50DD#64
  let iterations : Int := 2
  let w__0 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
  writeReg RC (vectorUpdate w__0 0 0x0000000000000000#64)
  let w__1 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
  writeReg RC (vectorUpdate w__1 1 0x13198A2E03707344#64)
  let w__2 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
  writeReg RC (vectorUpdate w__2 2 0xA4093822299F31D0#64)
  let iterations ← (( do
    if (isqarma3 : Bool)
    then (pure (2))
    else
      (do
        let iterations : Int := 4
        let w__3 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
        writeReg RC (vectorUpdate w__3 3 0x082EFA98EC4E6C89#64)
        let w__4 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
        writeReg RC (vectorUpdate w__4 4 0x452821E638D01377#64)
        (pure (iterations))) ) : SailM Int )
  let iterations : Int := iterations
  let modk0 : (BitVec 64) :=
    (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access key0 0)])) +++ (Sail.BitVec.extractLsb key0
          63 2)) +++ ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access key0 63)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
            key0 1)]))))
  let runningmod : (BitVec 64) := modifier
  let workingval : (BitVec 64) := (data ^^^ key0)
  let (roundkey, runningmod, workingval) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := iterations
    (do
      let mut loop_vars := (roundkey, runningmod, workingval)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (roundkey, runningmod, workingval) := loop_vars
        loop_vars ← do
          let roundkey : (BitVec 64) := (key1 ^^^ runningmod)
          let workingval : (BitVec 64) := (workingval ^^^ roundkey)
          let w__5 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
          let workingval :=
            ((workingval ^^^ (GetElem?.getElem! w__5 (Sail.Int.toNatChecked (i)))) : (BitVec 64))
          let workingval ← (( do
            if ((i >b 0) : Bool)
            then
              (do
                let w__6 ← (( do (PACCellShuffle workingval) ) : SailM (BitVec 64) )
                let workingval := (w__6 : (BitVec 64))
                (PACMult workingval))
            else (pure (workingval)) ) : SailM (BitVec 64) )
          let workingval ← (( do
            if (isqarma3 : Bool)
            then
              (do
                (PACSub1 workingval))
            else
              (do
                (PACSub workingval)) ) : SailM (BitVec 64) )
          let w__10 ← (( do (TweakShuffle (Sail.BitVec.extractLsb runningmod 63 0)) ) : SailM
            (BitVec 64) )
          let runningmod := (w__10 : (BitVec 64))
          (pure ((roundkey, runningmod, workingval)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  let roundkey : (BitVec 64) := (modk0 ^^^ runningmod)
  let workingval : (BitVec 64) := (workingval ^^^ roundkey)
  let w__11 ← (( do (PACCellShuffle workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__11 : (BitVec 64))
  let w__12 ← (( do (PACMult workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__12 : (BitVec 64))
  let workingval ← (( do
    if (isqarma3 : Bool)
    then
      (do
        (PACSub1 workingval))
    else
      (do
        (PACSub workingval)) ) : SailM (BitVec 64) )
  let w__15 ← (( do (PACCellShuffle workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__15 : (BitVec 64))
  let w__16 ← (( do (PACMult workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__16 : (BitVec 64))
  let workingval : (BitVec 64) := (key1 ^^^ workingval)
  let w__17 ← (( do (PACCellInvShuffle workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__17 : (BitVec 64))
  let workingval ← (( do
    if (isqarma3 : Bool)
    then
      (do
        (PACSub1 workingval))
    else
      (do
        (PACInvSub workingval)) ) : SailM (BitVec 64) )
  let w__20 ← (( do (PACMult workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__20 : (BitVec 64))
  let w__21 ← (( do (PACCellInvShuffle workingval) ) : SailM (BitVec 64) )
  let workingval : (BitVec 64) := (w__21 : (BitVec 64))
  let workingval : (BitVec 64) := (workingval ^^^ key0)
  let workingval : (BitVec 64) := (workingval ^^^ runningmod)
  let (roundkey, runningmod, workingval) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := iterations
    (do
      let mut loop_vars := (roundkey, runningmod, workingval)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (roundkey, runningmod, workingval) := loop_vars
        loop_vars ← do
          let workingval ← (( do
            if (isqarma3 : Bool)
            then
              (do
                (PACSub1 workingval))
            else
              (do
                (PACInvSub workingval)) ) : SailM (BitVec 64) )
          let workingval ← (( do
            if ((i <b iterations) : Bool)
            then
              (do
                let w__24 ← (( do (PACMult workingval) ) : SailM (BitVec 64) )
                let workingval := (w__24 : (BitVec 64))
                (PACCellInvShuffle workingval))
            else (pure (workingval)) ) : SailM (BitVec 64) )
          let w__26 ← (( do (TweakInvShuffle (Sail.BitVec.extractLsb runningmod 63 0)) ) : SailM
            (BitVec 64) )
          let runningmod := (w__26 : (BitVec 64))
          let roundkey : (BitVec 64) := (key1 ^^^ runningmod)
          let w__27 ← (( do readReg RC ) : SailM (Vector (BitVec 64) 5) )
          let workingval :=
            ((workingval ^^^ (GetElem?.getElem! w__27 (Sail.Int.toNatChecked ((iterations -i i))))) : (BitVec 64))
          let workingval : (BitVec 64) := (workingval ^^^ roundkey)
          let workingval : (BitVec 64) := (workingval ^^^ Alpha)
          (pure ((roundkey, runningmod, workingval)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  let workingval : (BitVec 64) := (workingval ^^^ modk0)
  (pure (workingval))


/-- Type quantifiers: k_isgeneric : Bool -/
def UsePACIMP (isgeneric : Bool) : SailM Bool := do
  if (isgeneric : Bool)
  then
    (do
      (HavePACIMPGeneric ()))
  else
    (do
      (HavePACIMPAuth ()))


/-- Type quantifiers: k_isgeneric : Bool -/
def UsePACQARMA3 (isgeneric : Bool) : SailM Bool := do
  if (isgeneric : Bool)
  then
    (do
      (HavePACQARMA3Generic ()))
  else
    (do
      (HavePACQARMA3Auth ()))


/-- Type quantifiers: k_isgeneric : Bool -/
def UsePACQARMA5 (isgeneric : Bool) : SailM Bool := do
  if (isgeneric : Bool)
  then
    (do
      (HavePACQARMA5Generic ()))
  else
    (do
      (HavePACQARMA5Auth ()))


def AArch64_ResetGeneralRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 30
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
        (X_set i 64 w__0)
    (pure loop_vars))


/-- Type quantifiers: alignment : Int, size : Int -/
def AllInAlignedQuantity (address : (BitVec 64)) (size : Int) (alignment : Int) : SailM Bool := do
  ArmFull.assert (size ≤b alignment) "sail-arm/v8_base.sail:22735.28-22735.29"
  (pure (((Align_bits (BitVec.subInt (BitVec.addInt address size) 1) alignment) == (Align_bits
        address alignment))))


/-- Type quantifiers: k_ex10456190_ : Bool -/
def C27bReservedBP64 (bt2_in : (BitVec 1)) (bt_in : (BitVec 4)) (context_aware : Bool) : SailM Bool := do
  let bt2 : (BitVec 1) := bt2_in
  let bt : (BitVec 4) := bt_in
  let reserved : Bool := false
  if ((bt2 == 0#1) : Bool)
  then
    (do
      let reserved : Bool :=
        if (((let b__1 := bt
             (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                        b__1 1 1)) == (0#1 : (BitVec 1)))) : Bool)
               then true
               else false : Bool))) && (! context_aware)) : Bool)
        then true
        else reserved
      let reserved : Bool :=
        if (((let b__2 := bt
             (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (1#1 : (BitVec 1))) : Bool)
             then true
             else false : Bool)) && (! (HaveEL EL2))) : Bool)
        then true
        else reserved
      let w__3 ← (( do
        if ((← do
             if ((let b__3 := bt
                (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
                then true
                else
                  (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
                  then true
                  else false) : Bool)) : Bool)
             then
               (do
                 let w__0 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
                 (pure (((! w__0) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__2 ← (( do (HaveV82Debug ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      let reserved : Bool :=
        if (w__3 : Bool)
        then true
        else reserved
      let w__6 ← (( do
        (pure ((← do
              if ((let b__5 := bt
                 (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__5 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
                 then true
                 else false : Bool)) : Bool)
              then
                (do
                  let w__4 ← (( do (HaveFeatABLE ()) ) : SailM Bool )
                  (pure (((! w__4) : Bool))))
              else (pure false)) && ((! (HaveAArch32EL EL1)) : Bool))) ) : SailM Bool )
      let reserved : Bool :=
        if (w__6 : Bool)
        then true
        else reserved
      (pure (reserved)))
  else
    (let reserved : Bool :=
      if ((let b__0 := bt
         (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                    b__0 1 1)) == (0#1 : (BitVec 1)))) : Bool)
           then true
           else false : Bool))) : Bool)
      then true
      else reserved
    (pure (reserved)))


def DebugAddrTop (_ : Unit) : SailM Int := do
  let w__0 ← (( do (Have56BitVAExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (55))
  else
    (do
      let w__1 ← (( do (Have52BitVAExt ()) ) : SailM Bool )
      let w__2 : Int :=
        if (w__1 : Bool)
        then 52
        else 48
      (pure (w__2)))


def __WriteGIC (offset : (BitVec 16)) (data : (BitVec 32)) : SailM Unit := do
  match offset with
  | 0x1004 => (pure ((gic_readonly offset)))
  | 0x1100 =>
    (let _ : Unit := (prerr_bits "[GIC] Registering interrupts " data)
    let intID : Int := (HighestSetBit data)
    (pure ((prerr_int "[GIC] Registering interrupt " intID))))
  | 0x1800 => (pure ((gic_readonly offset)))
  | 0x2000 =>
    (do
      let _ : Unit := (prerr_bits "[GIC] GICC_CTLR = " data)
      writeReg GICC_CTLR data)
  | 0x200C => (pure ((gic_readonly offset)))
  | 0x20FC => (pure ((gic_readonly offset)))
  | 0x2010 =>
    (do
      let _ : Unit := (prerr_bits "[GIC] End of interrupt = " data)
      (__GIC_ClearActiveInterrupt data))
  | 0x3000 =>
    (do
      let _ : Unit := (prerr_bits "[GIC] Deactivating interrupt " data)
      (__GIC_ClearActiveInterrupt data))
  | _ =>
    (let _ : Unit := (prerr_bits "[GIC] Unknown write offset: " offset)
    (pure ((prerr_bits "[GIC] Unknown write data: " data))))


def AArch64_S1IndirectBasePermissions (regime : Regime) (walkstate : TTWState) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) : SailM S1AccessControls := do
  let gcs ← (( do (undefined_bitvector_at (← occLabel 1421) 1) ) : SailM (BitVec 1) )
  let overlay ← (( do (undefined_bitvector_at (← occLabel 1422) 1) ) : SailM (BitVec 1) )
  let r ← (( do (undefined_bitvector_at (← occLabel 1423) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1424) 1) ) : SailM (BitVec 1) )
  let wxn ← (( do (undefined_bitvector_at (← occLabel 1425) 1) ) : SailM (BitVec 1) )
  let x ← (( do (undefined_bitvector_at (← occLabel 1426) 1) ) : SailM (BitVec 1) )
  let pgcs ← (( do (undefined_bitvector_at (← occLabel 1427) 1) ) : SailM (BitVec 1) )
  let pr ← (( do (undefined_bitvector_at (← occLabel 1428) 1) ) : SailM (BitVec 1) )
  let pw ← (( do (undefined_bitvector_at (← occLabel 1429) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 1430) 1) ) : SailM (BitVec 1) )
  let u_overlay ← (( do (undefined_bitvector_at (← occLabel 1431) 1) ) : SailM (BitVec 1) )
  let ugcs ← (( do (undefined_bitvector_at (← occLabel 1432) 1) ) : SailM (BitVec 1) )
  let ur ← (( do (undefined_bitvector_at (← occLabel 1433) 1) ) : SailM (BitVec 1) )
  let uw ← (( do (undefined_bitvector_at (← occLabel 1434) 1) ) : SailM (BitVec 1) )
  let uwxn ← (( do (undefined_bitvector_at (← occLabel 1435) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1436) 1) ) : SailM (BitVec 1) )
  let permissions : Permissions := walkstate.permissions
  let s1perms ← (( do (undefined_S1AccessControls (← occLabel 1437) ()) ) : SailM
    S1AccessControls )
  let (pgcs, pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    match permissions.ppi with
    | 0b0000 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0001 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0010 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0011 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0100 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0101 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0110 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b0111 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1000 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1001 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 0#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1010 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1011 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1100 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1101 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | 0b1110 =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
    | _ =>
      (let (tup__0, tup__1, tup__2, tup__3) :=
        ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let pgcs : (BitVec 1) := tup__3
      (pgcs, pr, pw, px))
  let p_overlay : (BitVec 1) :=
    (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.ppi 3)])))
  let pwxn : (BitVec 1) :=
    if ((permissions.ppi == 0b0110#4) : Bool)
    then 1#1
    else 0#1
  let (pgcs, pr, pw, px, u_overlay, ugcs, ur, uw, uwxn, ux) ← (( do
    if ((HasUnprivileged regime) : Bool)
    then
      (do
        let (ugcs, ur, uw, ux) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match permissions.upi with
          | 0b0000 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0001 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0010 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0011 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0100 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0101 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0110 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b0111 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1000 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1001 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1010 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1011 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1100 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1101 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | 0b1110 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
          | _ =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (ugcs, ur, uw, ux))
        let u_overlay : (BitVec 1) :=
          (Complement.complement
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.upi 3)])))
        let uwxn : (BitVec 1) :=
          if ((permissions.upi == 0b0110#4) : Bool)
          then 1#1
          else 0#1
        let (pgcs, pr, pw, px, ugcs, ur, uw, ux) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          if ((((px == 1#1) || (pgcs == 1#1)) && ((uw == 1#1) || (ugcs == 1#1))) : Bool)
          then
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let px : (BitVec 1) := tup__2
            let pgcs : (BitVec 1) := tup__3
            let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            let ugcs : (BitVec 1) := tup__3
            (pgcs, pr, pw, px, ugcs, ur, uw, ux))
          else (pgcs, pr, pw, px, ugcs, ur, uw, ux)
        let w__2 ← (( do
          (pure ((← do
                (pure ((← do
                      (HavePANExt ())) && (accdesc.pan : Bool)))) && ((! ((BEq.beq regime
                    Regime_EL10) && (walkparams.nv1 == 1#1))) : Bool))) ) : SailM Bool )
        let (pr, pw) ← (( do
          if (w__2 : Bool)
          then
            (do
              let w__4 ← (( do
                (pure ((← do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.PAN == 1#1) : Bool)))) && ((permissions.upi != 0b0000#4) : Bool)))
                ) : SailM Bool )
              let (pr, pw) : ((BitVec 1) × (BitVec 1)) :=
                if (w__4 : Bool)
                then
                  (let (tup__0, tup__1) := ((0#1, 0#1) : ((BitVec 1) × (BitVec 1)))
                  let pr : (BitVec 1) := tup__0
                  let pw : (BitVec 1) := tup__1
                  (pr, pw))
                else (pr, pw)
              (pure ((pr, pw))))
          else (pure ((pr, pw))) ) : SailM ((BitVec 1) × (BitVec 1)) )
        (pure ((pgcs, pr, pw, px, u_overlay, ugcs, ur, uw, uwxn, ux))))
    else (pure ((pgcs, pr, pw, px, u_overlay, ugcs, ur, uw, uwxn, ux))) ) : SailM
    ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1))
    )
  let uwxn := uwxn
  let u_overlay := u_overlay
  let (gcs, overlay, r, w, wxn, x) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    if ((accdesc.el == EL0) : Bool)
    then
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((ur, uw, ux, ugcs, uwxn, u_overlay) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let x : (BitVec 1) := tup__2
      let gcs : (BitVec 1) := tup__3
      let wxn : (BitVec 1) := tup__4
      let overlay : (BitVec 1) := tup__5
      (gcs, overlay, r, w, wxn, x))
    else
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((pr, pw, px, pgcs, pwxn, p_overlay) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let x : (BitVec 1) := tup__2
      let gcs : (BitVec 1) := tup__3
      let wxn : (BitVec 1) := tup__4
      let overlay : (BitVec 1) := tup__5
      (gcs, overlay, r, w, wxn, x))
  let (gcs, x) : ((BitVec 1) × (BitVec 1)) :=
    if (((BEq.beq accdesc.ss SS_Secure) && (BEq.beq walkstate.baseaddress.paspace PAS_NonSecure)) : Bool)
    then
      (let x : (BitVec 1) := (x &&& (Complement.complement walkparams.sif))
      let gcs : (BitVec 1) := 0#1
      (gcs, x))
    else (gcs, x)
  let (gcs, x) : ((BitVec 1) × (BitVec 1)) :=
    if (((BEq.beq accdesc.ss SS_Root) && (bne walkstate.baseaddress.paspace PAS_Root)) : Bool)
    then
      (let x : (BitVec 1) := 0#1
      let gcs : (BitVec 1) := 0#1
      (gcs, x))
    else (gcs, x)
  let (gcs, x) : ((BitVec 1) × (BitVec 1)) :=
    if ((((BEq.beq accdesc.ss SS_Realm) && ((BEq.beq regime Regime_EL2) || (BEq.beq regime
               Regime_EL20))) && (bne walkstate.baseaddress.paspace PAS_Realm)) : Bool)
    then
      (let x : (BitVec 1) := 0#1
      let gcs : (BitVec 1) := 0#1
      (gcs, x))
    else (gcs, x)
  let x := x
  let gcs := gcs
  let s1perms : S1AccessControls := { s1perms with r := r }
  let s1perms : S1AccessControls := { s1perms with w := w }
  let s1perms : S1AccessControls := { s1perms with x := x }
  let s1perms : S1AccessControls := { s1perms with gcs := gcs }
  let s1perms : S1AccessControls := { s1perms with wxn := wxn }
  let s1perms : S1AccessControls := { s1perms with overlay := (overlay == 1#1) }
  (pure (s1perms))


end ArmFull.Functions
