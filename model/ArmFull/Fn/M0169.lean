module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0119
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0150
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0154
public import ArmFull.Fn.M0155
public import ArmFull.Fn.M0156 set_option backward.proofsInPublic true @[expose] public section

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

def DecodeGPTBlock (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Block) "sail-inputs/03-v8_base.sail:19572.37-19572.38"
  let result ← (( do (undefined_GPTEntry (← occLabel 1227) ()) ) : SailM GPTEntry )
  if ((! (IsZero (Sail.BitVec.extractLsb entry 63 8))) : Bool)
  then
    (do
      let w__0 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailM GPTEntry )
      (pure ((GPCF_Walk, w__0))))
  else
    (do
      let w__1 ← (( do (GPIValid (Sail.BitVec.extractLsb entry 7 4)) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          let w__2 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailM GPTEntry )
          (pure ((GPCF_Walk, w__2))))
      else
        (do
          let result : GPTEntry := { result with gpi := (Sail.BitVec.extractLsb entry 7 4) }
          let result : GPTEntry := { result with level := 0 }
          let result : GPTEntry :=
            match pgs with
            | .PGS_4KB => { result with size := GPTRange_4KB }
            | .PGS_16KB => { result with size := GPTRange_16KB }
            | .PGS_64KB => { result with size := GPTRange_64KB }
          let w__3 ← (( do (GPTL0Size ()) ) : SailM Int )
          let result := ({ result with contig_size := w__3 } : GPTEntry)
          (pure ((GPCF_None, result)))))


def DecodeGPTContiguous (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := SailME.run do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Contig) "sail-inputs/03-v8_base.sail:19603.38-19603.39"
  let result ← (( do (undefined_GPTEntry (← occLabel 1228) ()) ) : SailME (GPCF × GPTEntry)
    GPTEntry )
  if ((! (IsZero (Sail.BitVec.extractLsb entry 63 10))) : Bool)
  then (pure ((GPCF_Walk, result)))
  else
    (do
      let result : GPTEntry := { result with gpi := (Sail.BitVec.extractLsb entry 7 4) }
      let w__0 ← (( do (GPIValid result.gpi) ) : SailME (GPCF × GPTEntry) Bool )
      if ((! w__0) : Bool)
      then (pure ((GPCF_Walk, result)))
      else
        (do
          let result : GPTEntry :=
            match pgs with
            | .PGS_4KB => { result with size := GPTRange_4KB }
            | .PGS_16KB => { result with size := GPTRange_16KB }
            | .PGS_64KB => { result with size := GPTRange_64KB }
          let result ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb entry 9 8)) with
            | 0b01 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_2MB }
              (pure (result)))
            | 0b10 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_32MB }
              (pure (result)))
            | 0b11 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_512MB }
              (pure (result)))
            | _ =>
              (do
                let w__1 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCF × GPTEntry) GPTEntry )
                SailME.throw ((GPCF_Walk, w__1) : (GPCF × GPTEntry))
                (pure (result))) ) : SailME (GPCF × GPTEntry) GPTEntry )
          let result : GPTEntry := { result with level := 1 }
          (pure ((GPCF_None, result)))))


/-- Type quantifiers: index : Int -/
def DecodeGPTGranules (pgs : PGSe) (index : Int) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := SailME.run do
  let result ← (( do (undefined_GPTEntry (← occLabel 1229) ()) ) : SailME (GPCF × GPTEntry)
    GPTEntry )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 15
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (GPIValid (BitVec.slice entry (Sail.Int.toNatChecked ((i *i 4))) 4)) ) :
          SailME (GPCF × GPTEntry) Bool )
        if ((! w__0) : Bool)
        then
          (do
            SailME.throw ((GPCF_Walk, result) : (GPCF × GPTEntry)))
        else (pure (()))
    (pure loop_vars))
  let result : GPTEntry :=
    { result with gpi := (BitVec.slice entry (Sail.Int.toNatChecked ((index *i 4))) 4) }
  let result : GPTEntry :=
    match pgs with
    | .PGS_4KB => { result with size := GPTRange_4KB }
    | .PGS_16KB => { result with size := GPTRange_16KB }
    | .PGS_64KB => { result with size := GPTRange_64KB }
  let result : GPTEntry := { result with contig_size := result.size }
  let result : GPTEntry := { result with level := 1 }
  (pure ((GPCF_None, result)))


def DecodeGPTTable (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTTable) := do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Table) "sail-inputs/03-v8_base.sail:19678.37-19678.38"
  let result ← (( do (undefined_GPTTable (← occLabel 1230) ()) ) : SailM GPTTable )
  if ((! (IsZero ((Sail.BitVec.extractLsb entry 63 52) +++ (Sail.BitVec.extractLsb entry 11 4)))) : Bool)
  then
    (do
      let w__0 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
      (pure ((GPCF_Walk, w__0))))
  else
    (do
      let l0sz ← (( do (GPTL0Size ()) ) : SailM Int )
      let p : Int := 12
      let p : Int :=
        match pgs with
        | .PGS_4KB => 12
        | .PGS_16KB => 14
        | .PGS_64KB => 16
      let p : Int := p
      if ((! (is_zero_subrange entry ((l0sz -i p) -i 2) 12)) : Bool)
      then
        (do
          let w__1 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
          (pure ((GPCF_Walk, w__1))))
      else
        (do
          let result : GPTTable :=
            match pgs with
            | .PGS_4KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 17) +++ (Zeros (n := 17))) }
            | .PGS_16KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 15) +++ (Zeros (n := 15))) }
            | .PGS_64KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 13) +++ (Zeros (n := 13))) }
          let w__2 ← (( do (AbovePPS result.address) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
              (pure ((GPCF_AddressSize, w__3))))
          else (pure ((GPCF_None, result)))))


def AlignmentFault (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 1251) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
  let fault : FaultRecord := { fault with level := 0 }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__0 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__0 } : FaultRecord)
  (pure (fault))


def ExclusiveFault (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 1252) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_Exclusive }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__0 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__0 } : FaultRecord)
  (pure (fault))


/-- Type quantifiers: k_isgeneric : Bool -/
def ComputePAC (data : (BitVec 64)) (modifier : (BitVec 64)) (key0 : (BitVec 64)) (key1 : (BitVec 64)) (isgeneric : Bool) : SailM (BitVec 64) := do
  let w__0 ← (( do (UsePACIMP isgeneric) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (ComputePACIMPDEF data modifier key0 key1))
  else
    (do
      let w__2 ← (( do (UsePACQARMA3 isgeneric) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let isqarma3 : Bool := true
          (ComputePACQARMA data modifier key0 key1 isqarma3))
      else
        (do
          let w__4 ← (( do (UsePACQARMA5 isgeneric) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let isqarma3 : Bool := false
              (ComputePACQARMA data modifier key0 key1 isqarma3))
          else
            (do
              (undefined_bitvector_at (← occLabel 1291) 64))))


/-- Type quantifiers: b : Int -/
def NumContextAwareBreakpointsImplemented (b : Int) : SailM Int := do
  (C27cEnsureDebugConfig ())
  let w__0 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  ArmFull.assert (b == w__0) "sail-inputs/29-armcert-c27c.sail:103.31-103.32"
  readReg __num_ctx_breakpoints


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 64 -/
def AArch64_WatchpointByteMatch (n : Nat) (vaddress : (BitVec 64)) : SailM Bool := SailME.run do
  let LSB ← (( do (undefined_bitvector_at (← occLabel 1397) 8) ) : SailME Bool (BitVec 8) )
  let MSB ← (( do (undefined_bitvector_at (← occLabel 1398) 8) ) : SailME Bool (BitVec 8) )
  let top ← (( do (DebugAddrTop ()) ) : SailME Bool Int )
  let w__0 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let bottom : Nat :=
    (Sail.Int.toNatChecked (if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             (GetElem?.getElem! w__0 n) 2)])) == 1#1) : Bool)
    then 2
    else 3))
  let bottom : Int := bottom
  let w__1 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let byte_select_match : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__1 n))
          (BitVec.toNat (Sail.BitVec.extractLsb vaddress (Sail.Int.toNatChecked ((bottom -i 1))) 0)))])) != 0#1)
  let w__2 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let mask : Int := (BitVec.toNat (_get_DBGWCR_EL1_Type_MASK (GetElem?.getElem! w__2 n)))
  let w__4 ← (( do
    if (((mask >b 0) : Bool) : Bool)
    then
      (do
        let w__3 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        (pure (((! (IsOnes (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__3 n)))) : Bool))))
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
        let w__6 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let w__7 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let LSB : (BitVec 8) :=
          ((_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__6 n)) &&& (Complement.complement
              (BitVec.subInt (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__7 n)) 1)))
        let w__8 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let MSB : (BitVec 8) := ((_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__8 n)) + LSB)
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
        let c ← (( do (undefined_Constraint (← occLabel 1399) ()) ) : SailME Bool Constraint )
        let w__10 ← (( do (ConstrainUnpredictableInteger 3 31 Unpredictable_RESWPMASK) ) : SailME
          Bool (Constraint × Int) )
        let (tup__0, tup__1) := (w__10 : (Constraint × Int))
        let c : Constraint := tup__0
        let mask : Int := tup__1
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
              c Constraint_UNKNOWN))) "sail-inputs/03-v8_base.sail:23742.88-23742.89"
        match c with
        | .Constraint_DISABLED =>
          (do
            SailME.throw (false : Bool)
            (pure (mask)))
        | .Constraint_NONE => (pure (0))
        | _ => (pure (mask)))
    else (pure (mask)) ) : SailME Bool Int )
  let mask : Int := mask
  let w__16 ← (( do
    if ((← do
         if ((← do
              if (((top <b 55) : Bool) : Bool)
              then
                (do
                  let w__11 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
                  (pure (((! (is_ones_subrange (GetElem?.getElem! w__11 n) 63 top)) : Bool))))
              else (pure false)) : Bool)
         then
           (do
             let w__13 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
             (pure (((! (is_zero_subrange (GetElem?.getElem! w__13 n) 63 top)) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_DBGxVR_RESS))
    else (pure false) ) : SailME Bool Bool )
  let top : Int :=
    if (w__16 : Bool)
    then 63
    else top
  let top : Int := top
  let WVR_match ← (( do (undefined_bool_at (← occLabel 1400) ()) ) : SailME Bool Bool )
  let WVR_match ← (( do
    if ((mask >b bottom) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b mask) && ((mask ≤b top) && (top <b 64))) "sail-inputs/03-v8_base.sail:23760.67-23760.68"
        let w__17 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (mask : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress (Sail.Int.toNatChecked (top)) (Sail.Int.toNatChecked (mask)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              (GetElem?.getElem! w__17 n) (Sail.Int.toNatChecked (top))
              (Sail.Int.toNatChecked (mask))))) : Bool)
        let w__19 ← (( do
          if ((WVR_match : Bool) : Bool)
          then
            (do
              let w__18 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
              (pure (((! (is_zero_subrange (GetElem?.getElem! w__18 n) (mask -i 1) bottom)) : Bool))))
          else (pure false) ) : SailME Bool Bool )
        if (w__19 : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_WPMASKEDBITS))
        else (pure (WVR_match)))
    else
      (do
        ArmFull.assert ((0 ≤b bottom) && ((bottom ≤b top) && (top <b 64))) "sail-inputs/03-v8_base.sail:23767.71-23767.72"
        let w__21 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (bottom : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress (Sail.Int.toNatChecked (top)) (Sail.Int.toNatChecked (bottom)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              (GetElem?.getElem! w__21 n) (Sail.Int.toNatChecked (top))
              (Sail.Int.toNatChecked (bottom))))) : Bool)
        (pure (WVR_match))) ) : SailME Bool Bool )
  (pure ((WVR_match && byte_select_match)))


/-- Type quantifiers: size : Nat, size > 0 -/
def PhysMemWrite (desc : AddressDescriptor) (size : Nat) (accdesc : AccessDescriptor) (translation_info : (Option TranslationInfo)) (data : (BitVec (8 * size))) : SailM PhysMemRetStatus := do
  let paddress := desc.paddress.address
  if (((size == 4) && ((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
           (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
           (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) GIC_BASE)))) : Bool)
  then
    (do
      (__WriteGIC (Sail.BitVec.extractLsb paddress 15 0) (Sail.BitVec.castWidth data))
      (pure ((CreatePhysMemRetStatus Fault_None))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
             (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
             (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) UART_BASE))) : Bool)
      then
        (let _ : Unit :=
          (__WriteUART (Sail.BitVec.extractLsb paddress 15 0) size (Sail.BitVec.castWidth data))
        (pure ((CreatePhysMemRetStatus Fault_None))))
      else
        (do
          let w__0 ← (( do
            (sail_mem_write
              (write_request accdesc translation_info size desc.vaddress desc.paddress.address
                (Sail.BitVec.castWidth data))) ) : SailM (Result (Option Bool) Fault) )
          let w__1 : PhysMemRetStatus :=
            match w__0 with
            | .Ok _ => (CreatePhysMemRetStatus Fault_None)
            | .Err statuscode => (CreatePhysMemRetStatus statuscode)
          (pure (w__1))))


/-- Type quantifiers: k_N : Nat, 11 < k_N -/
def AArch64_S2ApplyFWBMemAttrs (s1_memattrs : MemoryAttributes) (walkparams : S2TTWParams) (descriptor : (BitVec k_N)) : SailM MemoryAttributes := do
  let s2_device ← (( do (undefined_DeviceType (← occLabel 1552) ()) ) : SailM DeviceType )
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1553) ()) ) : SailM
    MemoryAttributes )
  let s2_attr : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
  let s2_sh ← (( do
    if ((walkparams.ds == 1#1) : Bool)
    then (pure (walkparams.sh))
    else
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26650.33-26650.34"
        (pure ((Sail.BitVec.extractLsb descriptor 9 8)))) ) : SailM (BitVec 2) )
  let s2_fnxs : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
  let memattrs ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access s2_attr 2)])) == 0#1) : Bool)
    then
      (do
        let s2_device ← (( do (DecodeDevice (Sail.BitVec.extractLsb s2_attr 1 0)) ) : SailM
          DeviceType )
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
        let memattrs : MemoryAttributes :=
          if ((BEq.beq s1_memattrs.memtype MemType_Device) : Bool)
          then { memattrs with device := (S2CombineS1Device s1_memattrs.device s2_device) }
          else { memattrs with device := s2_device }
        let memattrs : MemoryAttributes := { memattrs with xs := s1_memattrs.xs }
        (pure (memattrs)))
    else
      (do
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb s2_attr 1 0)) == 0b11#2) : Bool)
        then (pure (s1_memattrs))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb s2_attr 1 0)) == 0b10#2) : Bool)
            then
              (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
              let memattrs : MemoryAttributes :=
                { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
              let memattrs : MemoryAttributes :=
                { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
              let memattrs : MemoryAttributes :=
                if (((BEq.beq s1_memattrs.memtype MemType_Normal) && (s1_memattrs.inner.attrs != MemAttr_NC)) : Bool)
                then
                  (let memattrs : MemoryAttributes :=
                    { memattrs with inner := { memattrs.inner with hints := s1_memattrs.inner.hints } }
                  { memattrs with inner := { memattrs.inner with transient := s1_memattrs.inner.transient } })
                else
                  (let memattrs : MemoryAttributes :=
                    { memattrs with inner := { memattrs.inner with hints := MemHint_RWA } }
                  { memattrs with inner := { memattrs.inner with transient := false } })
              let memattrs : MemoryAttributes :=
                if (((BEq.beq s1_memattrs.memtype MemType_Normal) && (s1_memattrs.outer.attrs != MemAttr_NC)) : Bool)
                then
                  (let memattrs : MemoryAttributes :=
                    { memattrs with outer := { memattrs.outer with hints := s1_memattrs.outer.hints } }
                  { memattrs with outer := { memattrs.outer with transient := s1_memattrs.outer.transient } })
                else
                  (let memattrs : MemoryAttributes :=
                    { memattrs with outer := { memattrs.outer with hints := MemHint_RWA } }
                  { memattrs with outer := { memattrs.outer with transient := false } })
              let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
              (pure (memattrs)))
            else
              (do
                if ((BEq.beq s1_memattrs.memtype MemType_Device) : Bool)
                then (pure (s1_memattrs))
                else
                  (do
                    let cacheability_attr ← (( do (undefined_MemAttrHints (← occLabel 1554) ())
                      ) : SailM MemAttrHints )
                    let cacheability_attr : MemAttrHints :=
                      { cacheability_attr with attrs := MemAttr_NC }
                    let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                    let memattrs : MemoryAttributes := { memattrs with inner := cacheability_attr }
                    let memattrs : MemoryAttributes := { memattrs with outer := cacheability_attr }
                    let memattrs : MemoryAttributes := { memattrs with xs := s1_memattrs.xs }
                    (pure (memattrs)))))) ) : SailM MemoryAttributes )
  let s2_shareability ← (( do (DecodeShareability s2_sh) ) : SailM Shareability )
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (S2CombineS1Shareability s1_memattrs.shareability
        s2_shareability) }
  let w__0 ← (( do (S2MemTagType memattrs s1_memattrs.tags) ) : SailM MemTagType )
  let memattrs := ({ memattrs with tags := w__0 } : MemoryAttributes)
  let memattrs : MemoryAttributes :=
    { memattrs with notagaccess := (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb s2_attr
            3 1)) == 0b111#3) && (BEq.beq memattrs.tags MemTag_AllocationTagged)) }
  let memattrs : MemoryAttributes :=
    if ((s2_fnxs == 1#1) : Bool)
    then { memattrs with xs := 0#1 }
    else memattrs
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (EffectiveShareability memattrs) }
  (pure (memattrs))


def AArch64_S2InitialTTWState (ss : SecurityState) (walkparams : S2TTWParams) : SailM TTWState := do
  let walkstate ← (( do (undefined_TTWState (← occLabel 1555) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1556) ()) ) : SailM FullAddress )
  let w__0 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
  let ttbr : (BitVec 128) := (Sail.BitVec.zeroExtend w__0 128)
  let tablebase : FullAddress :=
    match ss with
    | .SS_NonSecure => { tablebase with paspace := PAS_NonSecure }
    | .SS_Realm => { tablebase with paspace := PAS_Realm }
    | _ => tablebase
  let w__1 ← (( do (AArch64_S2TTBaseAddress walkparams tablebase.paspace ttbr) ) : SailM
    (BitVec 56) )
  let tablebase := ({ tablebase with address := w__1 } : FullAddress)
  let walkstate : TTWState := { walkstate with baseaddress := tablebase }
  let w__2 ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let walkstate := ({ walkstate with level := w__2 } : TTWState)
  let walkstate : TTWState := { walkstate with istable := true }
  let w__3 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailM
    MemoryAttributes )
  let walkstate := ({ walkstate with memattrs := w__3 } : TTWState)
  (pure (walkstate))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S2NextWalkStateTable (currentstate : TTWState) (walkparams : S2TTWParams) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let skl ← (( do (undefined_bitvector_at (← occLabel 1564) 2) ) : SailM (BitVec 2) )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1565) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1566) ()) ) : SailM FullAddress )
  let w__0 ← (( do (AArch64_NextTableBase descriptor walkparams.d128 walkparams.ds walkparams.tgx)
    ) : SailM (BitVec 56) )
  let tablebase := ({ tablebase with address := w__0 } : FullAddress)
  let tablebase : FullAddress := { tablebase with paspace := currentstate.baseaddress.paspace }
  let nextstate : TTWState := { nextstate with istable := true }
  let nextstate ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26921.35-26921.36"
        let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
        let nextstate : TTWState :=
          { nextstate with level := ((currentstate.level +i (BitVec.toNat skl)) +i 1) }
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with level := (currentstate.level +i 1) }
      (pure (nextstate))) ) : SailM TTWState )
  let nextstate : TTWState := { nextstate with baseaddress := tablebase }
  let nextstate : TTWState := { nextstate with memattrs := currentstate.memattrs }
  (pure (nextstate))


def AArch64_SS2InitialTTWState (walkparams : S2TTWParams) (ipaspace : PASpace) : SailM TTWState := do
  let walkstate ← (( do (undefined_TTWState (← occLabel 1568) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1569) ()) ) : SailM FullAddress )
  let ttbr ← (( do (undefined_bitvector_at (← occLabel 1570) 128) ) : SailM (BitVec 128) )
  let ttbr ← (( do
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (do
        let w__0 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
        let ttbr := ((Sail.BitVec.zeroExtend w__0 128) : (BitVec 128))
        (pure (ttbr)))
    else
      (do
        let w__1 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
        let ttbr := ((Sail.BitVec.zeroExtend w__1 128) : (BitVec 128))
        (pure (ttbr))) ) : SailM (BitVec 128) )
  let tablebase : FullAddress :=
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (if ((walkparams.sw == 0#1) : Bool)
      then { tablebase with paspace := PAS_Secure }
      else { tablebase with paspace := PAS_NonSecure })
    else
      (if ((walkparams.nsw == 0#1) : Bool)
      then { tablebase with paspace := PAS_Secure }
      else { tablebase with paspace := PAS_NonSecure })
  let w__2 ← (( do (AArch64_S2TTBaseAddress walkparams tablebase.paspace ttbr) ) : SailM
    (BitVec 56) )
  let tablebase := ({ tablebase with address := w__2 } : FullAddress)
  let walkstate : TTWState := { walkstate with baseaddress := tablebase }
  let w__3 ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let walkstate := ({ walkstate with level := w__3 } : TTWState)
  let walkstate : TTWState := { walkstate with istable := true }
  let w__4 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailM
    MemoryAttributes )
  let walkstate := ({ walkstate with memattrs := w__4 } : TTWState)
  (pure (walkstate))


def GCSReturnValueCheckEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let questionMark := el
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__1 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_GCSCRE0_EL1_Type_RVCHKEN w__1) == 1#1))))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__2 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
              (pure (((_get_GCSCR_EL1_Type_RVCHKEN w__2) == 1#1))))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__3 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_GCSCR_EL2_Type_RVCHKEN w__3) == 1#1))))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__4 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
                      (pure (((_get_GCSCR_EL3_Type_RVCHKEN w__4) == 1#1))))
                  else
                    (do
                      (undefined_bool_at (← occLabel 1758) ()))))))


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg4 (cold : Bool) : SailM Bool := do
  let w__1465 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_P1_EL2 (Sail.BitVec.updateSubrange w__1465 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1466 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1466 63 56 0b00000000#8)
  let w__1467 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1467 43 41 0b000#3)
  let w__1468 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1468 31 28 0b0000#4)
  let w__1469 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange w__1469 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1470 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange w__1470 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1471 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg SPMSELR_EL0 (Sail.BitVec.updateSubrange w__1471 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1472 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg SPMSELR_EL0 (Sail.BitVec.updateSubrange w__1472 3 2 0b00#2)
  let w__1473 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1473 63 28
    0b000000000000000000000000000000000000#36)
  let w__1474 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1474 23 16 0b00000000#8)
  let w__1475 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1475 11 8 0b0000#4)
  let w__1476 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1476 63 (Bit 0#1))
  let w__1477 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1477 61 60 0b00#2)
  let w__1478 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1478 58 56 0b000#3)
  let w__1479 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1479 54 (Bit 0#1))
  let w__1480 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1480 50 (Bit 0#1))
  let w__1481 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1481 40 40 0#1)
  let w__1482 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1482 24 22 0b000#3)
  let w__1483 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1483 20 20 0#1)
  let w__1484 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1484 19 19 0#1)
  let w__1485 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1485 6 (Bit 0#1))
  let w__1486 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1486 5 4 0b11#2)
  let w__1487 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1487 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__1488 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1488 2 2 0#1)
  let w__1489 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1489 1 1 0#1)
  let w__1490 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1490 0 0 0#1)
  let w__1491 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__1491 63 32
    0b00000000000000000000000000000000#32)
  let w__1492 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__1492 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1493 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1493 63 (Bit 0#1))
  let w__1494 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1494 62 62 0#1)
  let w__1495 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1495 61 61 0#1)
  let w__1496 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1496 60 60 0#1)
  let w__1497 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1497 59 58 0b00#2)
  let w__1498 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1498 57 57 0#1)
  let w__1499 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1499 56 50 0b0000000#7)
  let w__1500 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1500 49 49 0#1)
  let w__1501 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1501 48 48 0#1)
  let w__1502 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1502 47 (Bit 0#1))
  let w__1503 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1503 46 46 0#1)
  let w__1504 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1504 45 45 0#1)
  let w__1505 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1505 44 44 0#1)
  let w__1506 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1506 43 (Bit 0#1))
  let w__1507 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1507 42 42 0#1)
  let w__1508 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1508 41 41 0#1)
  let w__1509 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1509 40 38 0b000#3)
  let w__1510 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1510 37 37 0#1)
  let w__1511 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1511 36 36 0#1)
  let w__1512 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1512 35 35 0#1)
  let w__1513 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1513 34 (Bit 0#1))
  let w__1514 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1514 33 33 0#1)
  let w__1515 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1515 32 32 0#1)
  let w__1516 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1516 31 31 0#1)
  let w__1517 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1517 30 (Bit 0#1))
  let w__1518 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1518 29 29 0#1)
  let w__1519 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1519 28 28 0#1)
  let w__1520 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1520 27 27 0#1)
  let w__1521 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1521 26 26 0#1)
  let w__1522 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1522 25 25 0#1)
  let w__1523 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1523 24 24 0#1)
  let w__1524 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1524 23 23 0#1)
  let w__1525 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1525 22 (Bit 0#1))
  let w__1526 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1526 21 21 0#1)
  let w__1527 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1527 20 20 0#1)
  let w__1528 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1528 19 19 0#1)
  let w__1529 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1529 18 18 0#1)
  let w__1530 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1530 17 17 0#1)
  let w__1531 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1531 16 16 0#1)
  let w__1533 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1532 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1532) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1533 : Bool)
  then
    (do
      let w__1534 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1534 15 15 0#1))
  else
    (do
      let w__1535 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__1536 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1535 15 15 w__1536))
  let w__1537 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1537 14 14 0#1)
  let w__1538 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1538 13 13 0#1)
  let w__1540 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1539 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1539) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1540 : Bool)
  then
    (do
      let w__1541 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1541 12 12 0#1))
  else
    (do
      let w__1542 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__1543 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1542 12 12 w__1543))
  let w__1544 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1544 11 11 0#1)
  let w__1545 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1545 10 10 0#1)
  let w__1546 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1546 9 (Bit 0#1))
  let w__1547 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1547 8 8 0#1)
  let w__1548 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1548 7 7 0#1)
  let w__1549 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1549 6 (Bit 0#1))
  let w__1550 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1550 5 5 0#1)
  let w__1551 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1551 4 4 0#1)
  let w__1552 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1552 3 3 0#1)
  let w__1553 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1553 2 2 0#1)
  let w__1554 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1554 1 1 0#1)
  let w__1555 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1555 0 0 0#1)
  let w__1556 ← (( do readReg CNTPS_TVAL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_TVAL_EL1 (Sail.BitVec.updateSubrange w__1556 63 32
    0b00000000000000000000000000000000#32)
  let w__1557 ← (( do readReg ID_AA64AFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR1_EL1 (Sail.BitVec.updateSubrange w__1557 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1558 ← (( do readReg LOREA_EL1 ) : SailM (BitVec 64) )
  writeReg LOREA_EL1 (Sail.BitVec.updateSubrange w__1558 63 56 0b00000000#8)
  let w__1559 ← (( do readReg LOREA_EL1 ) : SailM (BitVec 64) )
  writeReg LOREA_EL1 (Sail.BitVec.updateSubrange w__1559 15 0 0b0000000000000000#16)
  let w__1560 ← (( do readReg CNTV_TVAL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_TVAL_EL0 (Sail.BitVec.updateSubrange w__1560 63 32
    0b00000000000000000000000000000000#32)
  let w__1561 ← (( do readReg ICV_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_DIR_EL1 (Sail.BitVec.updateSubrange w__1561 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1562 ← (( do readReg ICC_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR1_EL1 (Sail.BitVec.updateSubrange w__1562 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1563 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__1563 63 40 0b000000000000000000000000#24)
  let w__1564 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (BitVec.update w__1564 31 (Bit 1#1))
  let w__1565 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__1565 29 25 0b00000#5)
  let w__1566 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1566 63 32
    0b00000000000000000000000000000000#32)
  let w__1567 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1567 31 8 0b000000000000000000000000#24)
  if (cold : Bool)
  then
    (do
      let w__1568 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
      writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1568 7 0 0b00000000#8))
  else (pure (()))
  let w__1569 ← (( do readReg ICV_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__1569 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1570 ← (( do readReg ID_AA64AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR0_EL1 (Sail.BitVec.updateSubrange w__1570 63 32
    0b00000000000000000000000000000000#32)
  let w__1571 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__1571 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__1572 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__1572 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1573 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__1573 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__1574 ← (( do readReg ICC_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR0_EL1 (Sail.BitVec.updateSubrange w__1574 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1575 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1575 63 60 0b0000#4)
  let w__1576 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1576 51 48 0b0000#4)
  let w__1577 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1577 39 36 0b0000#4)
  let w__1578 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1578 31 28 0b0000#4)
  let w__1579 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1579 15 8 0b00000000#8)
  let w__1580 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
  writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__1580 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1581 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
  writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__1581 8 4 0b00000#5)
  let w__1582 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
  writeReg ZCR_EL1 (Sail.BitVec.updateSubrange w__1582 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1583 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
  writeReg ZCR_EL1 (Sail.BitVec.updateSubrange w__1583 8 4 0b00000#5)
  let w__1584 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
  writeReg ZCR_EL2 (Sail.BitVec.updateSubrange w__1584 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1585 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
  writeReg ZCR_EL2 (Sail.BitVec.updateSubrange w__1585 8 4 0b00000#5)
  let w__1586 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1586 63 32 0b00000000000000000000000000000000#32)
  let w__1587 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1587 29 9 0b000000000000000000000#21)
  let w__1588 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1588 8 4 0b00000#5)
  let w__1589 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1589 63 32 0b00000000000000000000000000000000#32)
  let w__1590 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1590 29 9 0b000000000000000000000#21)
  let w__1591 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1591 8 4 0b00000#5)
  let w__1592 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1592 63 32 0b00000000000000000000000000000000#32)
  let w__1593 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1593 29 9 0b000000000000000000000#21)
  let w__1594 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1594 8 4 0b00000#5)
  let w__1595 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1595 62 60 0b000#3)
  let w__1596 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1596 51 49 0b000#3)
  let w__1597 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1597 41 40 0b00#2)
  let w__1598 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1598 31 0
    0b00000000000000000000000000000000#32)
  let w__1599 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1599 63 32
    0b00000000000000000000000000000000#32)
  let w__1600 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__1600 : Bool)
  then
    (do
      let w__1601 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
      let w__1602 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1601 31 31 w__1602))
  else
    (do
      let w__1604 ← (( do
        if (((! cold) : Bool) : Bool)
        then
          (do
            let w__1603 ← (( do (HaveEL EL3) ) : SailM Bool )
            (pure (((! w__1603) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1604 : Bool)
      then
        (do
          let w__1605 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
          writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1605 31 31 1#1))
      else (pure (())))
  let w__1606 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1606 30 9 0b0000000000000000000000#22)
  let w__1607 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1607 7 2 0b000000#6)
  let w__1608 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1608 63 62 0b00#2)
  let w__1609 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1609 56 40 0b00000000000000000#17)
  let w__1610 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1610 31 21 0b00000000000#11)
  let w__1611 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (BitVec.update w__1611 16 (Bit 0#1))
  let w__1612 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1612 63 63 0#1)
  let w__1613 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1613 62 59 0b0000#4)
  let w__1614 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (BitVec.update w__1614 57 (Bit 0#1))
  let w__1615 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1615 53 51 0b000#3)
  let w__1616 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__1616 : Bool)
  then
    (do
      let w__1617 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let w__1618 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1617 49 49 w__1618))
  else
    (do
      let w__1620 ← (( do
        if (((! cold) : Bool) : Bool)
        then
          (do
            let w__1619 ← (( do (HaveEL EL3) ) : SailM Bool )
            (pure (((! w__1619) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1620 : Bool)
      then
        (do
          let w__1621 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1621 49 49 1#1))
      else (pure (())))
  let w__1622 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__1622 : Bool)
  then
    (do
      let w__1623 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let w__1624 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1623 48 48 w__1624))
  else
    (do
      let w__1626 ← (( do
        if (((! cold) : Bool) : Bool)
        then
          (do
            let w__1625 ← (( do (HaveEL EL3) ) : SailM Bool )
            (pure (((! w__1625) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1626 : Bool)
      then
        (do
          let w__1627 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1627 48 48 1#1))
      else (pure (())))
  let w__1628 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_MPAMEN w__1628 0#1))
  let w__1629 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_TRAPLOWER w__1629 1#1))
  let w__1630 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 2 w__1630 58 0b00#2)))
  let w__1631 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 2 w__1631 53 0b00#2)))
  let w__1632 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 4 w__1632 48 0b0000#4)))
  let w__1633 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
  writeReg MPAM0_EL1 (Sail.BitVec.updateSubrange w__1633 63 48 0b0000000000000000#16)
  let w__1634 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1634 63 48 0b0000000000000000#16)
  let w__1635 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1635 39 32 0b00000000#8)
  let w__1636 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1636 15 0 0b0000000000000000#16)
  let w__1637 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (_update_MPAM1_EL1_Type_MPAMEN w__1637 0#1))
  let w__1638 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 2 w__1638 61 0b00#2)))
  let w__1639 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 5 w__1639 55 0b00000#5)))
  let w__1640 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 6 w__1640 48 0b000000#6)))
  let w__1641 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMVPMV_EL2 (Sail.BitVec.updateSubrange w__1641 63 32
    0b00000000000000000000000000000000#32)
  let w__1642 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
  writeReg GMID_EL1 (Sail.BitVec.updateSubrange w__1642 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__1643 ← (( do readReg TFSR_EL3 ) : SailM (BitVec 64) )
  writeReg TFSR_EL3 (Sail.BitVec.updateSubrange w__1643 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1644 ← (( do readReg TFSRE0_EL1 ) : SailM (BitVec 64) )
  writeReg TFSRE0_EL1 (Sail.BitVec.updateSubrange w__1644 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1645 ← (( do readReg TFSR_EL2 ) : SailM (BitVec 64) )
  writeReg TFSR_EL2 (Sail.BitVec.updateSubrange w__1645 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1646 ← (( do readReg TFSR_EL1 ) : SailM (BitVec 64) )
  writeReg TFSR_EL1 (Sail.BitVec.updateSubrange w__1646 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1647 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1647 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1648 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1648 7 4 0b0000#4)
  let w__1649 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1649 63 56 0b00000000#8)
  let w__1650 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1650 7 4 0b0000#4)
  let w__1651 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCR_EL1 (Sail.BitVec.updateSubrange w__1651 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__1652 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1652 63 18
    0b0000000000000000000000000000000000000000000000#46)
  let w__1653 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1653 16 11 0b000000#6)
  let w__1654 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1654 9 0 0b0000000000#10)
  let w__1655 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1655 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1656 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1656 15 4 0b000000000000#12)
  if (cold : Bool)
  then
    (do
      let w__1657 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1657 3 0 0b0000#4))
  else (pure (()))
  let w__1658 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1658 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1659 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1659 15 4 0b000000000000#12)
  if (cold : Bool)
  then
    (do
      let w__1660 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1660 3 0 0b0000#4))
  else (pure (()))
  let w__1661 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange w__1661 63 16
    0b000000000000000000000000000000000000000000000000#48)
  if (cold : Bool)
  then
    (do
      let w__1662 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange w__1662 15 0 0b0000000000000000#16))
  else (pure (()))
  let w__1663 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange w__1663 63 16
    0b000000000000000000000000000000000000000000000000#48)
  if (cold : Bool)
  then
    (do
      let w__1664 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange w__1664 15 0 0b0000000000000000#16))
  else (pure (()))
  let w__1665 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1665 63 32
    0b00000000000000000000000000000000#32)
  let w__1666 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1666 27 25 0b000#3)
  let w__1667 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1667 23 14 0b0000000000#10)
  let w__1668 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg AMUSERENR_EL0 (Sail.BitVec.updateSubrange w__1668 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1669 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__1669 63 32
    0b00000000000000000000000000000000#32)
  let w__1670 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange w__1670 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1671 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSFCR_EL1 (Sail.BitVec.updateSubrange w__1671 63 19
    0b000000000000000000000000000000000000000000000#45)
  let w__1672 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSFCR_EL1 (Sail.BitVec.updateSubrange w__1672 15 5 0b00000000000#11)
  let w__1673 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIRR_EL1 (Sail.BitVec.updateSubrange w__1673 63 32
    0b00000000000000000000000000000000#32)
  let w__1674 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIRR_EL1 (Sail.BitVec.updateSubrange w__1674 7 1 0b0000000#7)
  let w__1675 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__1675 55 32 0b000000000000000000000000#24)
  let w__1676 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSEVFR_EL1 (Sail.BitVec.updateSubrange w__1676 47 32 0b0000000000000000#16)
  let w__1677 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSEVFR_EL1 (BitVec.update w__1677 0 (Bit 0#1))
  let w__1678 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1678 11 6 0b000000#6)
  let w__1679 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1679 4 3 0b00#2)
  let w__1680 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1680 0 0 0#1)
  let w__1681 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1681 63 40 0b000000000000000000000000#24)
  let w__1682 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1682 36 32 0b00000#5)
  let w__1683 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1683 25 20 0b000000#6)
  let w__1684 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL2 (Sail.BitVec.updateSubrange w__1684 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1685 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL2 (BitVec.update w__1685 2 (Bit 0#1))
  let w__1686 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL1 (Sail.BitVec.updateSubrange w__1686 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1687 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL1 (BitVec.update w__1687 2 (Bit 0#1))
  let w__1688 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__1688 63 26
    0b00000000000000000000000000000000000000#38)
  let w__1689 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 (Sail.BitVec.updateSubrange w__1689 47 32 0b0000000000000000#16)
  let w__1690 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 (BitVec.update w__1690 0 (Bit 0#1))
  let w__1691 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__1691 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__1692 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__1692 7 6 0b00#2)
  let w__1693 ← (( do readReg PMSLATFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSLATFR_EL1 (Sail.BitVec.updateSubrange w__1693 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1694 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1694 63 32 0b00000000000000000000000000000000#32)
  let w__1695 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1695 30 25 0b000000#6)
  let w__1696 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1696 63 32 0b00000000000000000000000000000000#32)
  let w__1697 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1697 30 16 0b000000000000000#15)
  let w__1698 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1698 13 (Bit 0#1))
  let w__1699 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1699 11 (Bit 0#1))
  let w__1700 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1700 8 4 0b00000#5)
  let w__1701 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1701 63 32 0b00000000000000000000000000000000#32)
  let w__1702 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1702 30 16 0b000000000000000#15)
  let w__1703 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1703 13 (Bit 0#1))
  let w__1704 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1704 11 10 0b00#2)
  let w__1705 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1705 8 6 0b000#3)
  let w__1706 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange w__1706 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1707 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1707 63 32 0b00000000000000000000000000000000#32)
  let w__1708 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1708 30 25 0b000000#6)
  let w__1709 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1709 23 13 0b00000000000#11)
  let w__1710 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1710 8 6 0b000#3)
  let w__1711 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1711 63 32 0b00000000000000000000000000000000#32)
  let w__1712 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1712 30 25 0b000000#6)
  let w__1713 ← (( do readReg ERRSELR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRSELR_EL1 (Sail.BitVec.updateSubrange w__1713 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1714 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1714 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1715 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (BitVec.update w__1715 13 (Bit 0#1))
  let w__1716 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1716 11 0 0b000000000000#12)
  let w__1717 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1717 63 25
    0b000000000000000000000000000000000000000#39)
  let w__1718 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1718 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1720 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1720 : Bool)
  then
    (do
      let w__1721 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1722 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1721 23 23 w__1722))
  else (pure (()))
  let w__1724 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1723 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1723) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1724 : Bool)
  then
    (do
      let w__1725 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1726 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1725 23 23 w__1726))
  else (pure (()))
  let w__1728 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1728 : Bool)
  then
    (do
      let w__1729 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1730 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1729 22 22 w__1730))
  else (pure (()))
  let w__1732 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1731 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1731) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1732 : Bool)
  then
    (do
      let w__1733 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1734 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1733 22 22 w__1734))
  else (pure (()))
  let w__1735 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1735 21 10 0b000000000000#12)
  let w__1737 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1737 : Bool)
  then
    (do
      let w__1738 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1739 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1738 8 8 w__1739))
  else (pure (()))
  let w__1741 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1740 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1740) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1741 : Bool)
  then
    (do
      let w__1742 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1743 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1742 8 8 w__1743))
  else (pure (()))
  let w__1744 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (BitVec.update w__1744 7 (Bit 0#1))
  let w__1746 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1746 : Bool)
  then
    (do
      let w__1747 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1748 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1747 6 5 w__1748))
  else (pure (()))
  let w__1750 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1749 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1749) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1750 : Bool)
  then
    (do
      let w__1751 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1752 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1751 6 5 w__1752))
  else (pure (()))
  let w__1754 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1754 : Bool)
  then
    (do
      let w__1755 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1756 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1755 4 4 w__1756))
  else (pure (()))
  let w__1758 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1757 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1757) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1758 : Bool)
  then
    (do
      let w__1759 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1760 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1759 4 4 w__1760))
  else (pure (()))
  let w__1762 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1762 : Bool)
  then
    (do
      let w__1763 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1764 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1763 3 3 w__1764))
  else (pure (()))
  let w__1766 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1765 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1765) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1766 : Bool)
  then
    (do
      let w__1767 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1768 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1767 3 3 w__1768))
  else (pure (()))
  let w__1769 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (BitVec.update w__1769 2 (Bit 0#1))
  let w__1770 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1770 1 1 0#1)
  let w__1771 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1771 0 0 0#1)
  let w__1772 ← (( do readReg BRBTS_EL1 ) : SailM (BitVec 64) )
  writeReg BRBTS_EL1 (Sail.BitVec.updateSubrange w__1772 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1773 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1773 63 30
    0b0000000000000000000000000000000000#34)
  let w__1774 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1774 27 23 0b00000#5)
  let w__1776 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1776 : Bool)
  then
    (do
      let w__1777 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1778 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1777 22 22 w__1778))
  else (pure (()))
  let w__1780 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1779 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1779) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1780 : Bool)
  then
    (do
      let w__1781 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1782 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1781 22 22 w__1782))
  else (pure (()))
  let w__1784 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1784 : Bool)
  then
    (do
      let w__1785 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1786 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1785 21 21 w__1786))
  else (pure (()))
  let w__1788 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1787 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1787) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1788 : Bool)
  then
    (do
      let w__1789 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1790 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1789 21 21 w__1790))
  else (pure (()))
  let w__1792 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1792 : Bool)
  then
    (do
      let w__1793 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1794 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1793 20 20 w__1794))
  else (pure (()))
  let w__1796 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1795 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1795) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1796 : Bool)
  then
    (do
      let w__1797 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1798 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1797 20 20 w__1798))
  else (pure (()))
  let w__1800 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1800 : Bool)
  then
    (do
      let w__1801 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1802 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1801 19 19 w__1802))
  else (pure (()))
  let w__1804 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1803 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1803) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1804 : Bool)
  then
    (do
      let w__1805 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1806 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1805 19 19 w__1806))
  else (pure (()))
  let w__1808 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1808 : Bool)
  then
    (do
      let w__1809 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1810 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1809 18 18 w__1810))
  else (pure (()))
  let w__1812 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1811 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1811) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1812 : Bool)
  then
    (do
      let w__1813 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1814 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1813 18 18 w__1814))
  else (pure (()))
  let w__1816 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1816 : Bool)
  then
    (do
      let w__1817 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1818 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1817 17 17 w__1818))
  else (pure (()))
  let w__1820 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1819 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1819) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1820 : Bool)
  then
    (do
      let w__1821 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1822 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1821 17 17 w__1822))
  else (pure (()))
  let w__1824 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1824 : Bool)
  then
    (do
      let w__1825 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1826 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1825 16 16 w__1826))
  else (pure (()))
  let w__1828 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1827 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1827) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1828 : Bool)
  then
    (do
      let w__1829 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1830 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1829 16 16 w__1830))
  else (pure (()))
  let w__1831 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1831 15 8 0b00000000#8)
  let w__1833 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1833 : Bool)
  then
    (do
      let w__1834 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1835 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1834 7 7 w__1835))
  else (pure (()))
  let w__1837 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1836 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1836) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1837 : Bool)
  then
    (do
      let w__1838 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1839 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1838 7 7 w__1839))
  else (pure (()))
  (pure true)


end ArmFull.Functions
