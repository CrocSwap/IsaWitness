module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0014
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0155
public import ArmFull.Fn.M0180
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184 set_option backward.proofsInPublic true @[expose] public section

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

def StoreOnlyTagCheckingEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (HaveMTEStoreOnlyExt ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:22830.32-22830.33"
  let tcso ← (( do (undefined_bitvector_at (← occLabel 1353) 1) ) : SailM (BitVec 1) )
  let questionMark := el
  let tcso ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__1 ← (( do (ELIsInHost el) ) : SailM Bool )
        if ((! w__1) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL1_Type_TCSO0 w__2) : (BitVec 1))
            (pure (tcso)))
        else
          (do
            let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL2_Type_TCSO0 w__3) : (BitVec 1))
            (pure (tcso))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tcso := ((_get_SCTLR_EL1_Type_TCSO w__4) : (BitVec 1))
            (pure (tcso)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let tcso := ((_get_SCTLR_EL2_Type_TCSO w__5) : (BitVec 1))
                (pure (tcso)))
            else
              (do
                let w__6 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                let tcso := ((_get_SCTLR_EL3_Type_TCSO w__6) : (BitVec 1))
                (pure (tcso))))) ) : SailM (BitVec 1) )
  (pure ((tcso == 1#1)))


/-- Type quantifiers: k_N : Nat, k_s2fs1mro : Bool, k_N ≥ 0 -/
def AArch64_S1NextWalkStateTable (currentstate : TTWState) (s2fs1mro : Bool) (regime : Regime) (walkparams : S1TTWParams) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let skl ← (( do (undefined_bitvector_at (← occLabel 1497) 2) ) : SailM (BitVec 2) )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1498) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1499) ()) ) : SailM FullAddress )
  let w__0 ← (( do (AArch64_NextTableBase descriptor walkparams.d128 walkparams.ds walkparams.tgx)
    ) : SailM (BitVec 56) )
  let tablebase := ({ tablebase with address := w__0 } : FullAddress)
  let tablebase ← (( do
    if ((BEq.beq currentstate.baseaddress.paspace PAS_Secure) : Bool)
    then
      (do
        let nstable ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25642.39-25642.40"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
          else
            (do
              ArmFull.assert (63 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25645.38-25645.39"
              (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 63)]))))) ) : SailM
          (BitVec 1) )
        let tablebase : FullAddress :=
          { tablebase with paspace := if ((nstable == 0#1) : Bool)
            then PAS_Secure
            else PAS_NonSecure }
        (pure (tablebase)))
    else
      (let tablebase : FullAddress := { tablebase with paspace := currentstate.baseaddress.paspace }
      (pure (tablebase))) ) : SailM FullAddress )
  let nextstate : TTWState := { nextstate with istable := true }
  let nextstate : TTWState := { nextstate with nG := currentstate.nG }
  let nextstate ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25655.35-25655.36"
        let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
        let nextstate : TTWState :=
          { nextstate with level := ((currentstate.level +i (BitVec.toNat skl)) +i 1) }
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with level := (currentstate.level +i 1) }
      (pure (nextstate))) ) : SailM TTWState )
  let nextstate : TTWState := { nextstate with baseaddress := tablebase }
  let nextstate : TTWState := { nextstate with memattrs := currentstate.memattrs }
  let nextstate ← (( do
    if (((walkparams.hpd == 0#1) && (walkparams.pie == 0#1)) : Bool)
    then
      (do
        let w__1 ← (( do
          (AArch64_S1ApplyTablePerms currentstate.permissions descriptor regime walkparams) ) :
          SailM Permissions )
        let nextstate := ({ nextstate with permissions := w__1 } : TTWState)
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with permissions := currentstate.permissions }
      (pure (nextstate))) ) : SailM TTWState )
  let protectedbit ← (( do (undefined_bitvector_at (← occLabel 1500) 1) ) : SailM (BitVec 1) )
  let protectedbit ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (114 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25670.35-25670.36"
        let protectedbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 114)]))
        (pure (protectedbit)))
    else
      (do
        if ((walkparams.pnch == 1#1) : Bool)
        then
          (do
            ArmFull.assert (52 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25674.38-25674.39"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 52)])))))
        else (pure (0#1))) ) : SailM (BitVec 1) )
  let nextstate : TTWState :=
    if (((currentstate.s1assured && s2fs1mro) && (protectedbit == 1#1)) : Bool)
    then { nextstate with s1assured := true }
    else { nextstate with s1assured := false }
  let w__3 ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (112 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25684.35-25684.36"
        (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 112)])))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let nextstate := ({ nextstate with disch := w__3 } : TTWState)
  (pure (nextstate))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_NSS2TTWParams (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1504) ()) ) : SailM S2TTWParams )
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let walkparams :=
    ({ walkparams with vm := ((_get_HCR_EL2_Type_VM w__0) ||| (_get_HCR_EL2_Type_DC w__1)) } : S2TTWParams)
  let w__2 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let w__3 ← (( do (AArch64_S2DecodeTG0 (_get_VTCR_EL2_Type_TG0 w__2)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__3 } : S2TTWParams)
  let w__4 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_VTCR_EL2_Type_T0SZ w__4) } : S2TTWParams)
  let w__5 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_VTCR_EL2_Type_PS w__5) } : S2TTWParams)
  let w__6 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_VTCR_EL2_Type_IRGN0 w__6) } : S2TTWParams)
  let w__7 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_VTCR_EL2_Type_ORGN0 w__7) } : S2TTWParams)
  let w__8 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_VTCR_EL2_Type_SH0 w__8) } : S2TTWParams)
  let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__9) } : S2TTWParams)
  let w__10 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__12 ← (( do
    if (w__10 : Bool)
    then
      (do
        let w__11 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_D128 w__11))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__12 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        let w__13 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
        let walkparams := ({ walkparams with skl := (_get_VTTBR_EL2_Type_SKL w__13) } : S2TTWParams)
        (pure (walkparams)))
    else
      (do
        let w__14 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sl0 := (_get_VTCR_EL2_Type_SL0 w__14) } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__17 ← (( do
    if (((_get_HCR_EL2_Type_TGE w__15) == 0#1) : Bool)
    then
      (do
        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_PTW w__16))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ptw := w__17 } : S2TTWParams)
  let w__18 ← (( do (HaveStage2MemAttrControl ()) ) : SailM Bool )
  let w__20 ← (( do
    if (w__18 : Bool)
    then
      (do
        let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_FWB w__19))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with fwb := w__20 } : S2TTWParams)
  let w__21 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__23 ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HA w__22))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__23 } : S2TTWParams)
  let w__24 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__26 ← (( do
    if (w__24 : Bool)
    then
      (do
        let w__25 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HD w__25))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__26 } : S2TTWParams)
  let w__28 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__28 : Bool)
    then
      (do
        let w__29 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_VTCR_EL2_Type_DS w__29) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__31 ← (( do
    if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__31 : Bool)
    then
      (do
        let w__32 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let w__33 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with sl2 := ((_get_VTCR_EL2_Type_SL2 w__32) &&& (_get_VTCR_EL2_Type_DS w__33)) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__36 ← (( do
    if ((← do
         (HaveFeatCMOW ())) : Bool)
    then
      (do
        (IsHCRXEL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__38 ← (( do
    if (w__36 : Bool)
    then
      (do
        let w__37 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCRX_EL2_Type_CMOW w__37))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__38 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S2TTWParams := { walkparams with s2pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__39 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
        let w__41 ← (( do
          if (w__39 : Bool)
          then
            (do
              let w__40 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VTCR_EL2_Type_S2PIE w__40))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with s2pie := w__41 } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__42 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
  let w__44 ← (( do
    if (w__42 : Bool)
    then
      (do
        let w__43 ← (( do readReg S2PIR_EL2 ) : SailM (BitVec 64) )
        (pure ((Mk_S2PIRType w__43))))
    else (pure ((Mk_S2PIRType (Zeros (n := 64))))) ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with s2pir := w__44 } : S2TTWParams)
  let w__46 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 != 1#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__46 : Bool)
    then
      (do
        let w__47 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with assuredonly := (_get_VTCR_EL2_Type_AssuredOnly w__47) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with assuredonly := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__48 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__50 ← (( do
    if (w__48 : Bool)
    then
      (do
        let w__49 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL0 w__49))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl0 := w__50 } : S2TTWParams)
  let w__51 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__53 ← (( do
    if (w__51 : Bool)
    then
      (do
        let w__52 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL1 w__52))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl1 := w__53 } : S2TTWParams)
  let w__55 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  if (w__55 : Bool)
  then
    (do
      let w__56 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
      let walkparams := ({ walkparams with haft := (_get_VTCR_EL2_Type_HAFT w__56) } : S2TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S2TTWParams := { walkparams with haft := 0#1 }
    (pure (walkparams)))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_SS2TTWParams (ipaspace : PASpace) (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1507) ()) ) : SailM S2TTWParams )
  let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_D128 w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with d128 := w__2 } : S2TTWParams)
  let walkparams ← (( do
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (do
        let w__3 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
        let w__4 ← (( do (AArch64_S2DecodeTG0 (_get_VSTCR_EL2_Type_TG0 w__3)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__4 } : S2TTWParams)
        let w__5 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with txsz := (_get_VSTCR_EL2_Type_T0SZ w__5) } : S2TTWParams)
        let walkparams ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__6 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
              let walkparams :=
                ({ walkparams with skl := (_get_VSTTBR_EL2_Type_SKL w__6) } : S2TTWParams)
              (pure (walkparams)))
          else
            (do
              let w__7 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
              let walkparams :=
                ({ walkparams with sl0 := (_get_VSTCR_EL2_Type_SL0 w__7) } : S2TTWParams)
              (pure (walkparams))) ) : SailM S2TTWParams )
        let w__9 ← (( do
          if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
          then
            (do
              (Have52BitIPAAndPASpaceExt ()))
          else (pure false) ) : SailM Bool )
        if (w__9 : Bool)
        then
          (do
            let w__10 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
            let w__11 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with sl2 := ((_get_VSTCR_EL2_Type_SL2 w__10) &&& (_get_VTCR_EL2_Type_DS
                    w__11)) } : S2TTWParams)
            (pure (walkparams)))
        else
          (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
          (pure (walkparams))))
    else
      (do
        if ((BEq.beq ipaspace PAS_NonSecure) : Bool)
        then
          (do
            let w__12 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let w__13 ← (( do (AArch64_S2DecodeTG0 (_get_VTCR_EL2_Type_TG0 w__12)) ) : SailM TGx )
            let walkparams := ({ walkparams with tgx := w__13 } : S2TTWParams)
            let w__14 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with txsz := (_get_VTCR_EL2_Type_T0SZ w__14) } : S2TTWParams)
            let walkparams ← (( do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  let w__15 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  let walkparams :=
                    ({ walkparams with skl := (_get_VTTBR_EL2_Type_SKL w__15) } : S2TTWParams)
                  (pure (walkparams)))
              else
                (do
                  let w__16 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                  let walkparams :=
                    ({ walkparams with sl0 := (_get_VTCR_EL2_Type_SL0 w__16) } : S2TTWParams)
                  (pure (walkparams))) ) : SailM S2TTWParams )
            let w__18 ← (( do
              if (((BEq.beq walkparams.tgx TGx_4KB) : Bool) : Bool)
              then
                (do
                  (Have52BitIPAAndPASpaceExt ()))
              else (pure false) ) : SailM Bool )
            if (w__18 : Bool)
            then
              (do
                let w__19 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                let w__20 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                let walkparams :=
                  ({ walkparams with sl2 := ((_get_VTCR_EL2_Type_SL2 w__19) &&& (_get_VTCR_EL2_Type_DS
                        w__20)) } : S2TTWParams)
                (pure (walkparams)))
            else
              (let walkparams : S2TTWParams := { walkparams with sl2 := 0#1 }
              (pure (walkparams))))
        else
          (do
            (Unreachable ())
            (pure (walkparams)))) ) : SailM S2TTWParams )
  let w__21 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sw := (_get_VSTCR_EL2_Type_SW w__21) } : S2TTWParams)
  let w__22 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with nsw := (_get_VTCR_EL2_Type_NSW w__22) } : S2TTWParams)
  let w__23 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sa := (_get_VSTCR_EL2_Type_SA w__23) } : S2TTWParams)
  let w__24 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with nsa := (_get_VTCR_EL2_Type_NSA w__24) } : S2TTWParams)
  let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let walkparams :=
    ({ walkparams with vm := ((_get_HCR_EL2_Type_VM w__25) ||| (_get_HCR_EL2_Type_DC w__26)) } : S2TTWParams)
  let w__27 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_VTCR_EL2_Type_PS w__27) } : S2TTWParams)
  let w__28 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_VTCR_EL2_Type_IRGN0 w__28) } : S2TTWParams)
  let w__29 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_VTCR_EL2_Type_ORGN0 w__29) } : S2TTWParams)
  let w__30 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_VTCR_EL2_Type_SH0 w__30) } : S2TTWParams)
  let w__31 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__31) } : S2TTWParams)
  let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let w__34 ← (( do
    if (((_get_HCR_EL2_Type_TGE w__32) == 0#1) : Bool)
    then
      (do
        let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_PTW w__33))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ptw := w__34 } : S2TTWParams)
  let w__35 ← (( do (HaveStage2MemAttrControl ()) ) : SailM Bool )
  let w__37 ← (( do
    if (w__35 : Bool)
    then
      (do
        let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_FWB w__36))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with fwb := w__37 } : S2TTWParams)
  let w__38 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__40 ← (( do
    if (w__38 : Bool)
    then
      (do
        let w__39 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HA w__39))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__40 } : S2TTWParams)
  let w__41 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__43 ← (( do
    if (w__41 : Bool)
    then
      (do
        let w__42 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_HD w__42))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__43 } : S2TTWParams)
  let w__45 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__45 : Bool)
    then
      (do
        let w__46 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_VTCR_EL2_Type_DS w__46) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__49 ← (( do
    if ((← do
         (HaveFeatCMOW ())) : Bool)
    then
      (do
        (IsHCRXEL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__51 ← (( do
    if (w__49 : Bool)
    then
      (do
        let w__50 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCRX_EL2_Type_CMOW w__50))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__51 } : S2TTWParams)
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S2TTWParams := { walkparams with s2pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__52 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
        let w__54 ← (( do
          if (w__52 : Bool)
          then
            (do
              let w__53 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VTCR_EL2_Type_S2PIE w__53))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with s2pie := w__54 } : S2TTWParams)
        (pure (walkparams))) ) : SailM S2TTWParams )
  let w__55 ← (( do (HaveS2PIExt ()) ) : SailM Bool )
  let w__57 ← (( do
    if (w__55 : Bool)
    then
      (do
        let w__56 ← (( do readReg S2PIR_EL2 ) : SailM (BitVec 64) )
        (pure ((Mk_S2PIRType w__56))))
    else (pure ((Mk_S2PIRType (Zeros (n := 64))))) ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with s2pir := w__57 } : S2TTWParams)
  let w__59 ← (( do
    (pure ((← do
          (HaveTHExt ())) && ((walkparams.d128 != 1#1) : Bool))) ) : SailM Bool )
  let walkparams ← (( do
    if (w__59 : Bool)
    then
      (do
        let w__60 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with assuredonly := (_get_VTCR_EL2_Type_AssuredOnly w__60) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with assuredonly := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let w__61 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__63 ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL0 w__62))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl0 := w__63 } : S2TTWParams)
  let w__64 ← (( do (HaveTHExt ()) ) : SailM Bool )
  let w__66 ← (( do
    if (w__64 : Bool)
    then
      (do
        let w__65 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_VTCR_EL2_Type_TL1 w__65))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tl1 := w__66 } : S2TTWParams)
  let w__68 ← (( do
    (pure ((← do
          (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool))) ) : SailM Bool
    )
  let walkparams ← (( do
    if (w__68 : Bool)
    then
      (do
        let w__69 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_VTCR_EL2_Type_HAFT w__69) } : S2TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S2TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S2TTWParams )
  let walkparams : S2TTWParams := { walkparams with emec := 0#1 }
  (pure (walkparams))


end ArmFull.Functions
