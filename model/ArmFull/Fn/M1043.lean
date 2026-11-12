import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168
import ArmFull.Fn.M0173
import ArmFull.Fn.M0188
import ArmFull.Fn.M0216
import ArmFull.Fn.M0217
import ArmFull.Fn.M0218
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852
import ArmFull.Fn.M1002

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

/-- Type quantifiers: k_aligned : Bool, k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch64_MemSingle_set__1 (address : (BitVec 64)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) (ispair : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "sail-arm/v8_base.sail:28072.69-28072.70"
  let accdesc : AccessDescriptor := accdesc_in
  let w__0 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (AllInAlignedQuantity address size 16) ) : SailM Bool )
      ArmFull.assert w__1 "sail-arm/v8_base.sail:28075.54-28075.55")
  else
    (do
      ArmFull.assert (IsAligned__1 address size) "sail-arm/v8_base.sail:28077.42-28077.43")
  let w__3 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__3 : Bool)
    then
      (do
        let w__4 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__4 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) size)
    else ()
  let w__5 ← (( do (HaveTME ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__7 ← (( do
        if ((accdesc.transactional : Bool) : Bool)
        then
          (do
            let w__6 ← (( do (MemHasTransactionalAccess memaddrdesc.memattrs) ) : SailM Bool )
            (pure (((! w__6) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          (FailTransaction TMFailure_IMP false))
      else (pure (())))
  else (pure (()))
  let w__9 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__10 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__10) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let w__11 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let is_load : Bool := false
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure (()))
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1636) ()) ) : SailM
    PhysMemRetStatus )
  let atomic ← (( do (undefined_bool_at (← occLabel 1637) ()) ) : SailM Bool )
  let atomic ← (( do
    if ((((BEq.beq memaddrdesc.memattrs.memtype MemType_Normal) && (memaddrdesc.memattrs.inner.attrs == MemAttr_WB)) && (memaddrdesc.memattrs.outer.attrs == MemAttr_WB)) : Bool)
    then (pure (true))
    else
      (do
        if (((((accdesc.exclusive || accdesc.atomicop) || accdesc.acqsc) || accdesc.acqpc) || accdesc.relsc) : Bool)
        then
          (do
            let w__13 ← (( do
              if (((! aligned) : Bool) : Bool)
              then
                (do
                  let w__12 ← (( do (ConstrainUnpredictableBool Unpredictable_MISALIGNEDATOMIC) )
                    : SailM Bool )
                  (pure (((! w__12) : Bool))))
              else (pure false) ) : SailM Bool )
            if (w__13 : Bool)
            then
              (do
                let w__14 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                (AArch64_Abort address w__14)
                (pure (atomic)))
            else (pure (true)))
        else
          (do
            if (aligned : Bool)
            then
              (let atomic : Bool := (! ispair)
              (pure (atomic)))
            else
              (do
                (__IMPDEF_boolean "FEAT_LSE2: access is atomic")))) ) : SailM Bool )
  if (atomic : Bool)
  then
    (do
      let memstatus ← (( do
        (PhysMemWrite memaddrdesc size accdesc none (Sail.BitVec.castWidth value_name)) ) : SailM
        PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc size accdesc))
      else (pure (())))
  else
    (do
      if ((aligned && ispair) : Bool)
      then
        (do
          ArmFull.assert ((size == 8) || (size == 16)) "sail-arm/v8_base.sail:28128.37-28128.38"
          let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
          let highhalf ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1638)
              (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
            (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
          let lowhalf ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1639)
              (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
            (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
          let highhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
              (Sail.Int.toNatChecked (((size *i 8) -i 1)))
              (Sail.Int.toNatChecked (((((size *i 8) -i 1) -i (halfsize *i 8)) +i 1)))))
          let lowhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
              (Sail.Int.toNatChecked ((((size *i 8) -i 1) -i (halfsize *i 8))))
              (Sail.Int.toNatChecked ((((((size *i 8) -i 1) -i (halfsize *i 8)) -i (halfsize *i 8)) +i 1)))))
          let w__16 ← (( do
            (PhysMemWrite memaddrdesc halfsize accdesc none (Sail.BitVec.castWidth lowhalf)) ) :
            SailM PhysMemRetStatus )
          let memstatus : PhysMemRetStatus := (w__16 : PhysMemRetStatus)
          if ((IsFault__2 memstatus) : Bool)
          then
            (do
              (HandleExternalWriteAbort memstatus memaddrdesc halfsize accdesc))
          else (pure (()))
          let memaddrdesc : AddressDescriptor :=
            { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                  memaddrdesc.paddress.address halfsize) } }
          let memstatus ← (( do
            (PhysMemWrite memaddrdesc halfsize accdesc none (Sail.BitVec.castWidth highhalf)) ) :
            SailM PhysMemRetStatus )
          if ((IsFault__2 memstatus) : Bool)
          then
            (do
              (HandleExternalWriteAbort memstatus memaddrdesc halfsize accdesc))
          else (pure (())))
      else
        (do
          let (memaddrdesc, memstatus) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := (Sail.Int.toNatChecked ((size -i 1)))
            (do
              let mut loop_vars := (memaddrdesc, memstatus)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (memaddrdesc, memstatus) := loop_vars
                loop_vars ← do
                  let w__17 ← (( do
                    (PhysMemWrite memaddrdesc 1 accdesc none
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                        (Sail.Int.toNatChecked (((8 *i i) +i 7))) (Sail.Int.toNatChecked ((8 *i i))))))
                    ) : SailM PhysMemRetStatus )
                  let memstatus := (w__17 : PhysMemRetStatus)
                  if ((IsFault__2 memstatus) : Bool)
                  then
                    (do
                      (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc))
                  else (pure (()))
                  let memaddrdesc : AddressDescriptor :=
                    { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                          memaddrdesc.paddress.address 1) } }
                  (pure ((memaddrdesc, memstatus)))
              (pure loop_vars)) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
          (pure (()))))


/-- Type quantifiers: k_size : Nat, k_size ≥ 0 -/
def MemAtomic (address : (BitVec 64)) (cmpoperand : (BitVec k_size)) (operand : (BitVec k_size)) (accdesc_in : AccessDescriptor) : SailM (BitVec k_size) := do
  ArmFull.assert accdesc_in.atomicop "sail-arm/v8_base.sail:28335.30-28335.31"
  let bytes : Nat := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length operand) 8)))
  ArmFull.assert ((bytes == 1) || ((bytes == 2) || ((bytes == 4) || ((bytes == 8) || (bytes == 16))))) "sail-arm/v8_base.sail:28337.74-28337.75"
  let newvalue ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1654)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_size) )
  let oldvalue ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1655)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_size) )
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address bytes)
  let w__1 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__2 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let w__4 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address bytes))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__5))
  else (pure (()))
  let memaddrdesc ← (( do
    (AArch64_TranslateAddress address accdesc aligned (Sail.BitVec.length operand)) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then
      (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) (Sail.BitVec.length operand))
    else ()
  let w__11 ← (( do
    if ((← do
         (pure ((← do
               (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool)))) : Bool)
    then
      (do
        if ((← do
             let w__8 ← (( do (HaveMTEStoreOnlyExt ()) ) : SailM Bool )
             (pure (((! w__8) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__9 ← (( do (StoreOnlyTagCheckingEnabled accdesc.el) ) : SailM Bool )
            (pure (((! w__9) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__12 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__12) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1656) ()) ) : SailM
    PhysMemRetStatus )
  ArmFull.assert ((8 *i bytes) == (Sail.BitVec.length operand)) "sail-arm/v8_base.sail:28363.42-28363.43"
  let w__13 ← (( do
    ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc bytes accdesc
      none)) ) : SailM (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked bytes)))) )
  let (tup__0, tup__1) :=
    (w__13 : (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked bytes)))))
  let memstatus : PhysMemRetStatus := tup__0
  let oldvalue : (BitVec k_size) := (Sail.BitVec.castWidth tup__1)
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      (HandleExternalReadAbort memstatus memaddrdesc bytes accdesc))
  else (pure (()))
  let w__14 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let oldvalue : (BitVec k_size) :=
    if (w__14 : Bool)
    then (reverse_endianness oldvalue)
    else oldvalue
  let oldvalue := oldvalue
  let cmpfail : Bool := false
  let (cmpfail, newvalue) : (Bool × (BitVec k_size)) :=
    match accdesc.modop with
    | .MemAtomicOp_ADD =>
      (let newvalue : (BitVec k_size) := (oldvalue + operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_BIC =>
      (let newvalue : (BitVec k_size) := (oldvalue &&& (Complement.complement operand))
      (cmpfail, newvalue))
    | .MemAtomicOp_EOR =>
      (let newvalue : (BitVec k_size) := (oldvalue ^^^ operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_ORR =>
      (let newvalue : (BitVec k_size) := (oldvalue ||| operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_SMAX =>
      (let newvalue : (BitVec k_size) :=
        (Sail.BitVec.castWidth (integer_subrange
          (Max.max (BitVec.toInt oldvalue) (BitVec.toInt operand))
          ((Sail.BitVec.length operand) -i 1) 0))
      (cmpfail, newvalue))
    | .MemAtomicOp_SMIN =>
      (let newvalue : (BitVec k_size) :=
        (Sail.BitVec.castWidth (integer_subrange
          (Min.min (BitVec.toInt oldvalue) (BitVec.toInt operand))
          ((Sail.BitVec.length operand) -i 1) 0))
      (cmpfail, newvalue))
    | .MemAtomicOp_UMAX =>
      (let newvalue : (BitVec k_size) :=
        (Sail.BitVec.castWidth (integer_subrange
          (Max.max (BitVec.toNat oldvalue) (BitVec.toNat operand))
          ((Sail.BitVec.length operand) -i 1) 0))
      (cmpfail, newvalue))
    | .MemAtomicOp_UMIN =>
      (let newvalue : (BitVec k_size) :=
        (Sail.BitVec.castWidth (integer_subrange
          (Min.min (BitVec.toNat oldvalue) (BitVec.toNat operand))
          ((Sail.BitVec.length operand) -i 1) 0))
      (cmpfail, newvalue))
    | .MemAtomicOp_SWP =>
      (let newvalue : (BitVec k_size) := operand
      (cmpfail, newvalue))
    | .MemAtomicOp_CAS =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (cmpoperand != oldvalue)
      (cmpfail, newvalue))
    | .MemAtomicOp_GCSSS1 =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (cmpoperand != oldvalue)
      (cmpfail, newvalue))
  let w__17 ← (( do
    if ((← do
         (HaveMTEStoreOnlyExt ())) : Bool)
    then
      (do
        (StoreOnlyTagCheckingEnabled accdesc.el))
    else (pure false) ) : SailM Bool )
  let accdesc ← (( do
    if (w__17 : Bool)
    then
      (do
        let accdesc ← (( do
          if ((accdesc.tagchecked && cmpfail) : Bool)
          then
            (do
              let w__18 ← (( do (ConstrainUnpredictableBool Unpredictable_STOREONLYTAGCHECKEDCAS)
                ) : SailM Bool )
              let accdesc := ({ accdesc with tagchecked := w__18 } : AccessDescriptor)
              (pure (accdesc)))
          else (pure (accdesc)) ) : SailM AccessDescriptor )
        let w__20 ← (( do
          (pure ((← do
                (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
        if (w__20 : Bool)
        then
          (do
            let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
            let w__21 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
            if ((! w__21) : Bool)
            then
              (do
                let accdesc : AccessDescriptor := { accdesc with read := false }
                (AArch64_TagCheckFault address accdesc)
                (pure (accdesc)))
            else (pure (accdesc)))
        else (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  if ((! cmpfail) : Bool)
  then
    (do
      let w__22 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
      let newvalue : (BitVec k_size) :=
        if (w__22 : Bool)
        then (reverse_endianness newvalue)
        else newvalue
      let memstatus ← (( do
        (PhysMemWrite memaddrdesc bytes accdesc none (Sail.BitVec.castWidth newvalue)) ) : SailM
        PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc bytes accdesc))
      else (pure (())))
  else (pure (()))
  let w__23 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__23 : Bool)
  then
    (do
      let is_load : Bool := false
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure (()))
  (pure ((Sail.BitVec.castWidth oldvalue)))


/-- Type quantifiers: k_size : Nat, k_size ≥ 0 -/
def MemAtomicRCW (address : (BitVec 64)) (cmpoperand : (BitVec k_size)) (operand : (BitVec k_size)) (accdesc_in : AccessDescriptor) : SailM ((BitVec 4) × (BitVec k_size)) := do
  ArmFull.assert accdesc_in.atomicop "sail-arm/v8_base.sail:28582.30-28582.31"
  ArmFull.assert accdesc_in.rcw "sail-arm/v8_base.sail:28583.25-28583.26"
  let bytes : Nat := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length operand) 8)))
  ArmFull.assert ((bytes == 8) || (bytes == 16)) "sail-arm/v8_base.sail:28585.35-28585.36"
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 1660) 4) ) : SailM (BitVec 4) )
  let oldvalue ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1661)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_size) )
  let newvalue ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1662)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_size) )
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address bytes)
  let w__1 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__2 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let w__4 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address bytes))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__5))
  else (pure (()))
  let memaddrdesc ← (( do
    (AArch64_TranslateAddress address accdesc aligned (Sail.BitVec.length operand)) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then
      (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) (Sail.BitVec.length operand))
    else ()
  let w__11 ← (( do
    if ((← do
         (pure ((← do
               (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool)))) : Bool)
    then
      (do
        if ((← do
             let w__8 ← (( do (HaveMTEStoreOnlyExt ()) ) : SailM Bool )
             (pure (((! w__8) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__9 ← (( do (StoreOnlyTagCheckingEnabled accdesc.el) ) : SailM Bool )
            (pure (((! w__9) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__12 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__12) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1663) ()) ) : SailM
    PhysMemRetStatus )
  ArmFull.assert ((8 *i bytes) == (Sail.BitVec.length operand)) "sail-arm/v8_base.sail:28612.42-28612.43"
  let w__13 ← (( do
    ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc bytes accdesc
      none)) ) : SailM (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked bytes)))) )
  let (tup__0, tup__1) :=
    (w__13 : (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked bytes)))))
  let memstatus : PhysMemRetStatus := tup__0
  let oldvalue : (BitVec k_size) := (Sail.BitVec.castWidth tup__1)
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      (HandleExternalReadAbort memstatus memaddrdesc bytes accdesc))
  else (pure (()))
  let w__14 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let oldvalue : (BitVec k_size) :=
    if (w__14 : Bool)
    then (reverse_endianness oldvalue)
    else oldvalue
  let oldvalue := oldvalue
  let cmpfail : Bool := false
  let (cmpfail, newvalue) : (Bool × (BitVec k_size)) :=
    match accdesc.modop with
    | .MemAtomicOp_BIC =>
      (let newvalue : (BitVec k_size) := (oldvalue &&& (Complement.complement operand))
      (cmpfail, newvalue))
    | .MemAtomicOp_ORR =>
      (let newvalue : (BitVec k_size) := (oldvalue ||| operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_SWP =>
      (let newvalue : (BitVec k_size) := operand
      (cmpfail, newvalue))
    | .MemAtomicOp_CAS =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (oldvalue != cmpoperand)
      (cmpfail, newvalue))
    | _ => (cmpfail, newvalue)
  let nzcv ← (( do
    if (cmpfail : Bool)
    then (pure (0b1010#4))
    else
      (do
        (RCWCheck oldvalue newvalue accdesc.rcws)) ) : SailM (BitVec 4) )
  let w__18 ← (( do
    if ((← do
         (HaveMTEStoreOnlyExt ())) : Bool)
    then
      (do
        (StoreOnlyTagCheckingEnabled accdesc.el))
    else (pure false) ) : SailM Bool )
  let accdesc ← (( do
    if (w__18 : Bool)
    then
      (do
        let accdesc ← (( do
          if ((accdesc.tagchecked && cmpfail) : Bool)
          then
            (do
              let w__19 ← (( do (ConstrainUnpredictableBool Unpredictable_STOREONLYTAGCHECKEDCAS)
                ) : SailM Bool )
              let accdesc := ({ accdesc with tagchecked := w__19 } : AccessDescriptor)
              (pure (accdesc)))
          else (pure (accdesc)) ) : SailM AccessDescriptor )
        let w__21 ← (( do
          (pure ((← do
                (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
        if (w__21 : Bool)
        then
          (do
            let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
            let w__22 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
            if ((! w__22) : Bool)
            then
              (do
                let accdesc : AccessDescriptor := { accdesc with read := false }
                (AArch64_TagCheckFault address accdesc)
                (pure (accdesc)))
            else (pure (accdesc)))
        else (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  if ((nzcv == 0b0010#4) : Bool)
  then
    (do
      let w__23 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
      let newvalue : (BitVec k_size) :=
        if (w__23 : Bool)
        then (reverse_endianness newvalue)
        else newvalue
      let memstatus ← (( do
        (PhysMemWrite memaddrdesc bytes accdesc none (Sail.BitVec.castWidth newvalue)) ) : SailM
        PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc bytes accdesc))
      else (pure (())))
  else (pure (()))
  (pure ((nzcv, oldvalue)))


def MemStore64B (address : (BitVec 64)) (value_name : (BitVec 512)) (accdesc_in : AccessDescriptor) : SailM Unit := do
  let c ← (( do (undefined_Constraint (← occLabel 1670) ()) ) : SailM Constraint )
  let size : Nat := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  let w__1 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address size))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  let w__4 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__5 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) 64)
    else ()
  let w__7 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__8 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__8) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1671) ()) ) : SailM
    PhysMemRetStatus )
  let w__9 ← (( do (AddressSupportsLS64 memaddrdesc.paddress.address) ) : SailM Bool )
  if ((! w__9) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_LS64UNSUPPORTED) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_LIMITED_ATOMICITY) || (BEq.beq c Constraint_FAULT)) "sail-arm/v8_base.sail:28823.72-28823.73"
      if ((BEq.beq c Constraint_FAULT) : Bool)
      then
        (do
          let w__10 ← (( do (ExclusiveFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__10))
      else
        (do
          let (memaddrdesc, memstatus) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Int := (size -i 1)
            (do
              let mut loop_vars := (memaddrdesc, memstatus)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (memaddrdesc, memstatus) := loop_vars
                loop_vars ← do
                  let w__11 ← (( do
                    (PhysMemWrite memaddrdesc 1 accdesc none
                      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                        (Sail.Int.toNatChecked (((8 *i i) +i 7))) (Sail.Int.toNatChecked ((8 *i i))))))
                    ) : SailM PhysMemRetStatus )
                  let memstatus := (w__11 : PhysMemRetStatus)
                  if ((IsFault__2 memstatus) : Bool)
                  then
                    (do
                      (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc))
                  else (pure (()))
                  let memaddrdesc : AddressDescriptor :=
                    { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                          memaddrdesc.paddress.address 1) } }
                  (pure ((memaddrdesc, memstatus)))
              (pure loop_vars)) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
          (pure (()))))
  else
    (do
      let memstatus ← (( do
        (PhysMemWrite memaddrdesc size accdesc none (Sail.BitVec.castWidth value_name)) ) : SailM
        PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc size accdesc))
      else (pure (())))


end ArmFull.Functions
