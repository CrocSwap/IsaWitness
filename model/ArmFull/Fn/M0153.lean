module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0037
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0118
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

def IFAR_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFAR_Type := value_name
  let w__0 ← (( do (HaveEL EL2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
      writeReg FAR_EL2 (Sail.BitVec.updateSubrange w__1 63 32 (BitVec.slice r 0 32)))
  else
    (do
      let w__2 ← (( do (HIFAR_read ()) ) : SailM (BitVec 32) )
      (HIFAR_write (set_slice 32 w__2 0 (BitVec.slice r 0 32))))
  writeReg _IFAR_S r


def ReportAsGPCException (fault : FaultRecord) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:15091.20-15091.21"
  ArmFull.assert ((BEq.beq fault.statuscode Fault_GPCFOnWalk) || (BEq.beq fault.statuscode
      Fault_GPCFOnOutput)) "sail-inputs/03-v8_base.sail:15092.88-15092.89"
  ArmFull.assert (bne fault.gpcf.gpf GPCF_None) "sail-inputs/03-v8_base.sail:15093.38-15093.39"
  match fault.gpcf.gpf with
  | .GPCF_Walk => (pure (true))
  | .GPCF_AddressSize => (pure (true))
  | .GPCF_EABT => (pure (true))
  | .GPCF_Fail =>
    (do
      if ((← do
           let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
           (pure ((((_get_SCR_EL3_Type_GPF w__1) == 1#1) : Bool)))) : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__2.EL != EL3) : Bool))))
      else (pure false))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 879) ()))


def EncodePARAttrs (memattrs : MemoryAttributes) : SailM (BitVec 8) := SailME.run do
  let result ← (( do (undefined_bitvector_at (← occLabel 1188) 8) ) : SailME (BitVec 8)
    (BitVec 8) )
  let w__1 ← (( do
    (pure ((← do
          (HaveMTEExt ())) && ((BEq.beq memattrs.tags MemTag_AllocationTagged) : Bool))) ) : SailME
    (BitVec 8) Bool )
  if (w__1 : Bool)
  then
    (do
      let w__3 ← (( do
        (pure ((← do
              (HaveMTEPermExt ())) && (memattrs.notagaccess : Bool))) ) : SailME (BitVec 8) Bool )
      let result : (BitVec 8) :=
        if (w__3 : Bool)
        then (Sail.BitVec.updateSubrange result 7 0 0b11100000#8)
        else (Sail.BitVec.updateSubrange result 7 0 0b11110000#8)
      (pure (result)))
  else
    (do
      if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
      then
        (let result : (BitVec 8) := (Sail.BitVec.updateSubrange result 7 4 0b0000#4)
        let result : (BitVec 8) :=
          match memattrs.device with
          | .DeviceType_nGnRnE => (Sail.BitVec.updateSubrange result 3 0 0b0000#4)
          | .DeviceType_nGnRE => (Sail.BitVec.updateSubrange result 3 0 0b0100#4)
          | .DeviceType_nGRE => (Sail.BitVec.updateSubrange result 3 0 0b1000#4)
          | .DeviceType_GRE => (Sail.BitVec.updateSubrange result 3 0 0b1100#4)
        let result : (BitVec 8) :=
          (BitVec.update result 0 (Bit (Complement.complement memattrs.xs)))
        (pure (result)))
      else
        (do
          if ((memattrs.xs == 0#1) : Bool)
          then
            (do
              if (((((memattrs.outer.attrs == MemAttr_WT) && (memattrs.inner.attrs == MemAttr_WT)) && (! memattrs.outer.transient)) && (memattrs.outer.hints == MemHint_RA)) : Bool)
              then
                (do
                  SailME.throw (0b10100000#8 : (BitVec 8)))
              else
                (do
                  if (((memattrs.outer.attrs == MemAttr_NC) && (memattrs.inner.attrs == MemAttr_NC)) : Bool)
                  then
                    (do
                      SailME.throw (0b01000000#8 : (BitVec 8)))
                  else (pure (()))))
          else (pure (()))
          let result : (BitVec 8) :=
            if ((memattrs.outer.attrs == MemAttr_WT) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 7 6
                  (if (memattrs.outer.transient : Bool)
                  then 0b00#2
                  else 0b10#2))
              (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
            else
              (if ((memattrs.outer.attrs == MemAttr_WB) : Bool)
              then
                (let result : (BitVec 8) :=
                  (Sail.BitVec.updateSubrange result 7 6
                    (if (memattrs.outer.transient : Bool)
                    then 0b01#2
                    else 0b11#2))
                (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
              else (Sail.BitVec.updateSubrange result 7 4 0b0100#4))
          let result : (BitVec 8) :=
            if ((memattrs.inner.attrs == MemAttr_WT) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 3 2
                  (if (memattrs.inner.transient : Bool)
                  then 0b00#2
                  else 0b10#2))
              (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints))
            else
              (if ((memattrs.inner.attrs == MemAttr_WB) : Bool)
              then
                (let result : (BitVec 8) :=
                  (Sail.BitVec.updateSubrange result 3 2
                    (if (memattrs.inner.transient : Bool)
                    then 0b01#2
                    else 0b11#2))
                (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints))
              else (Sail.BitVec.updateSubrange result 3 0 0b0100#4))
          (pure (result))))


def WalkMemAttrs (sh : (BitVec 2)) (irgn : (BitVec 2)) (orgn : (BitVec 2)) : SailM MemoryAttributes := do
  let walkmemattrs ← (( do (undefined_MemoryAttributes (← occLabel 1216) ()) ) : SailM
    MemoryAttributes )
  let walkmemattrs : MemoryAttributes := { walkmemattrs with memtype := MemType_Normal }
  let w__0 ← (( do (DecodeShareability sh) ) : SailM Shareability )
  let walkmemattrs := ({ walkmemattrs with shareability := w__0 } : MemoryAttributes)
  let w__1 ← (( do (DecodeSDFAttr irgn) ) : SailM MemAttrHints )
  let walkmemattrs := ({ walkmemattrs with inner := w__1 } : MemoryAttributes)
  let w__2 ← (( do (DecodeSDFAttr orgn) ) : SailM MemAttrHints )
  let walkmemattrs := ({ walkmemattrs with outer := w__2 } : MemoryAttributes)
  let walkmemattrs : MemoryAttributes := { walkmemattrs with tags := MemTag_Untagged }
  let walkmemattrs : MemoryAttributes :=
    if (((walkmemattrs.inner.attrs == MemAttr_WB) && (walkmemattrs.outer.attrs == MemAttr_WB)) : Bool)
    then { walkmemattrs with xs := 0#1 }
    else { walkmemattrs with xs := 1#1 }
  let walkmemattrs : MemoryAttributes := { walkmemattrs with notagaccess := false }
  (pure (walkmemattrs))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def S1ConstrainUnpredictableRESMAIR (attr : (BitVec 8)) (s1aarch64 : Bool) : SailM Bool := do
  let b__0 := attr
  if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 7 4)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
           b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
  then
    (do
      let w__1 ← (( do
        if ((s1aarch64 : Bool) : Bool)
        then
          (do
            (HaveFeatXS ()))
        else (pure false) ) : SailM Bool )
      (pure ((! w__1))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 7 4)) == (0x0#4 : (BitVec 4))) : Bool)
      then (pure (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb attr 1 0)) != 0b00#2)))
      else
        (do
          match b__0 with
          | 0b01000000 =>
            (do
              let w__3 ← (( do
                if ((s1aarch64 : Bool) : Bool)
                then
                  (do
                    (HaveFeatXS ()))
                else (pure false) ) : SailM Bool )
              (pure ((! w__3))))
          | 0b10100000 =>
            (do
              let w__5 ← (( do
                if ((s1aarch64 : Bool) : Bool)
                then
                  (do
                    (HaveFeatXS ()))
                else (pure false) ) : SailM Bool )
              (pure ((! w__5))))
          | 0b11110000 =>
            (do
              let w__7 ← (( do
                if ((s1aarch64 : Bool) : Bool)
                then
                  (do
                    (HaveMTE2Ext ()))
                else (pure false) ) : SailM Bool )
              (pure ((! w__7))))
          | b__0 =>
            (pure (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 3 0)) == (0x0#4 : (BitVec 4))) : Bool)
              then true
              else false))))


def S2MemTagType (s2_memattrs : MemoryAttributes) (s1_tagtype : MemTagType) : SailM MemTagType := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  let w__1 : MemTagType :=
    if ((! w__0) : Bool)
    then MemTag_Untagged
    else
      (if (((((((((BEq.beq s1_tagtype MemTag_AllocationTagged) && (BEq.beq s2_memattrs.memtype
                         MemType_Normal)) && (s2_memattrs.inner.attrs == MemAttr_WB)) && (s2_memattrs.inner.hints == MemHint_RWA)) && (! s2_memattrs.inner.transient)) && (s2_memattrs.outer.attrs == MemAttr_WB)) && (s2_memattrs.outer.hints == MemHint_RWA)) && (! s2_memattrs.outer.transient)) : Bool)
      then MemTag_AllocationTagged
      else
        (if ((bne s1_tagtype MemTag_AllocationTagged) : Bool)
        then s1_tagtype
        else MemTag_Untagged))
  (pure (w__1))


/-- Type quantifiers: k_s2aarch64 : Bool -/
def S2DecodeMemAttrs (attr : (BitVec 4)) (sh : (BitVec 2)) (s2aarch64 : Bool) : SailM MemoryAttributes := do
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1220) ()) ) : SailM
    MemoryAttributes )
  let b__0 := attr
  let memattrs ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
        let w__0 ← (( do (DecodeDevice (Sail.BitVec.extractLsb attr 1 0)) ) : SailM DeviceType )
        let memattrs := ({ memattrs with device := w__0 } : MemoryAttributes)
        (pure (memattrs)))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do
              if ((s2aarch64 : Bool) : Bool)
              then
                (do
                  (HaveMTEPermExt ()))
              else (pure false) ) : SailM Bool )
            if (w__2 : Bool)
            then
              (do
                let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                let w__3 ← (( do (S2DecodeCacheability 0b11#2) ) : SailM MemAttrHints )
                let memattrs := ({ memattrs with outer := w__3 } : MemoryAttributes)
                let w__4 ← (( do (S2DecodeCacheability 0b11#2) ) : SailM MemAttrHints )
                let memattrs := ({ memattrs with inner := w__4 } : MemoryAttributes)
                (pure (memattrs)))
            else
              (do
                let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                let w__5 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 3 2)) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with outer := w__5 } : MemoryAttributes)
                let w__6 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 1 0)) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with inner := w__6 } : MemoryAttributes)
                (pure (memattrs))))
        | _ =>
          (do
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let w__7 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 3 2)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with outer := w__7 } : MemoryAttributes)
            let w__8 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 1 0)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with inner := w__8 } : MemoryAttributes)
            (pure (memattrs)))) ) : SailM MemoryAttributes )
  let w__9 ← (( do (DecodeShareability sh) ) : SailM Shareability )
  let memattrs := ({ memattrs with shareability := w__9 } : MemoryAttributes)
  let w__11 ← (( do
    if ((s2aarch64 : Bool) : Bool)
    then
      (do
        (HaveMTEPermExt ()))
    else (pure false) ) : SailM Bool )
  let memattrs : MemoryAttributes :=
    if (w__11 : Bool)
    then { memattrs with notagaccess := (attr == 0b0100#4) }
    else { memattrs with notagaccess := false }
  (pure (memattrs))


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
          ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:19511.35-19511.36"
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


def AArch64_ResetSpecialRegisters (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SP_EL0 w__0
  let w__1 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SP_EL1 w__1
  let w__2 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__2)
  let w__3 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg ELR_EL1 w__3
  let w__4 ← (( do (HaveEL EL2) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SP_EL2 w__5
      let w__6 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__6)
      let w__7 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL2 w__7)
  else (pure (()))
  let w__8 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      let w__9 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SP_EL3 w__9
      let w__10 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type w__10)
      let w__11 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL3 w__11)
  else (pure (()))
  let w__12 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
  if (w__12 : Bool)
  then
    (do
      let w__13 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
      let w__14 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__13 31 0 w__14)
      let w__15 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
      let w__16 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_irq (Sail.BitVec.updateSubrange w__15 31 0 w__16)
      let w__17 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
      let w__18 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_abt (Sail.BitVec.updateSubrange w__17 31 0 w__18)
      let w__19 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
      let w__20 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_und (Sail.BitVec.updateSubrange w__19 31 0 w__20))
  else (pure (()))
  let w__21 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DLR_EL0 w__21
  let w__22 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__22)


/-- Type quantifiers: alignment : Int, size : Int -/
def AllInAlignedQuantity (address : (BitVec 64)) (size : Int) (alignment : Int) : SailM Bool := do
  ArmFull.assert (size ≤b alignment) "sail-inputs/03-v8_base.sail:22745.28-22745.29"
  (pure (((Align_bits (BitVec.subInt (BitVec.addInt address size) 1) alignment) == (Align_bits
        address alignment))))


end ArmFull.Functions
