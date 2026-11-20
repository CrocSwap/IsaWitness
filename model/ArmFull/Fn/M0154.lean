module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_ex10380614_ : Bool -/
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
      let w__1 ← (( do
        if ((let b__2 := bt
           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (1#1 : (BitVec 1))) : Bool)
           then true
           else false : Bool)) : Bool)
        then
          (do
            let w__0 ← (( do (HaveEL EL2) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      let reserved : Bool :=
        if (w__1 : Bool)
        then true
        else reserved
      let w__5 ← (( do
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
                 let w__2 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
                 (pure (((! w__2) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__4 ← (( do (HaveV82Debug ()) ) : SailM Bool )
            (pure (((! w__4) : Bool))))
        else (pure false) ) : SailM Bool )
      let reserved : Bool :=
        if (w__5 : Bool)
        then true
        else reserved
      let w__9 ← (( do
        if ((← do
             if ((let b__5 := bt
                (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__5 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
                then true
                else false : Bool)) : Bool)
             then
               (do
                 let w__6 ← (( do (HaveFeatABLE ()) ) : SailM Bool )
                 (pure (((! w__6) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__8 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
            (pure (((! w__8) : Bool))))
        else (pure false) ) : SailM Bool )
      let reserved : Bool :=
        if (w__9 : Bool)
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


/-- Type quantifiers: k_aligned : Bool -/
def AArch64_S1HasAlignmentFault (accdesc : AccessDescriptor) (aligned : Bool) (ntlsmd : (BitVec 1)) (memattrs : MemoryAttributes) : SailM Bool := do
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveMTEExt ())) && (accdesc.tagaccess : Bool)))) && (accdesc.write : Bool))) )
        : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          if (((BEq.beq memattrs.memtype MemType_Device) : Bool) : Bool)
          then
            (do
              let w__3 ← (( do (ConstrainUnpredictable Unpredictable_DEVICETAGSTORE) ) : SailM
                Constraint )
              (pure (((BEq.beq w__3 Constraint_FAULT) : Bool))))
          else (pure false))
      else
        (pure (if ((accdesc.a32lsmd && (ntlsmd == 0#1)) : Bool)
          then ((BEq.beq memattrs.memtype MemType_Device) && (bne memattrs.device DeviceType_GRE))
          else
            (if ((BEq.beq accdesc.acctype AccessType_DCZero) : Bool)
            then (BEq.beq memattrs.memtype MemType_Device)
            else ((BEq.beq memattrs.memtype MemType_Device) && (! aligned))))))


def AArch64_TLBContextEL2 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1473) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL2 }
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__0 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR0_EL2_Type_CnP w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let tlbcontext := ({ tlbcontext with cnp := w__2 } : TLBContext)
  (pure (tlbcontext))


def AArch64_TLBContextEL20 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1474) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL20 }
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let w__3 ← (( do
    if (((_get_TCR_EL2_Type_A1 w__0) == 0#1) : Bool)
    then
      (do
        let w__1 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR0_EL2_Type_ASID w__1))))
    else
      (do
        let w__2 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
        (pure ((_get_TTBR1_EL2_Type_ASID w__2)))) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with asid := w__3 } : TLBContext)
  let w__4 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let tlbcontext : TLBContext :=
    if (((_get_TCR_EL2_Type_AS w__4) == 0#1) : Bool)
    then
      { tlbcontext with asid := (Sail.BitVec.updateSubrange tlbcontext.asid 15 8 (Zeros (n := 8))) }
    else tlbcontext
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__5 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      if ((BEq.beq (AArch64_GetVARange va) VARange_LOWER) : Bool)
      then
        (do
          let w__6 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR0_EL2_Type_CnP w__6) } : TLBContext)
          (pure (tlbcontext)))
      else
        (do
          let w__7 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR1_EL2_Type_CnP w__7) } : TLBContext)
          (pure (tlbcontext))))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


end ArmFull.Functions
