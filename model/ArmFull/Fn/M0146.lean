import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0118
import ArmFull.Fn.M0119

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

def HaveIDSExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_IDST)


def HaveFrintExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FRINTTS)


def HaveE0PDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_E0PD)


def HaveGTGExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_GTG)


def HaveSBExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SB)


def HaveMTEAsyncExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE4)


def HaveMTEPermExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE_PERM)


def HaveDGHExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DGH)


def HaveBF16Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_BF16)


def HaveEBF16 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_EBF16)


def HaveAArch32BF16Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AA32BF16)


def HaveFGTExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FGT)


def HaveInt8MatMulExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_I8MM)


def HaveAArch32Int8MatMulExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AA32I8MM)


def HavePMUv3p4 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3p4)


def HaveDoPD (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DoPD)


def Have56BitVAExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LVA3)


def Have128BitDescriptorExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_D128)


def HaveAIEExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AIE)


def HaveFeatTCR2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TCR2)


def HavePAN3Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PAN3)


def HaveFeatLS64_V (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LS64_V)


def HaveFeatLS64_ACCDATA (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LS64_ACCDATA)


def HaveFeatXS (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_XS)


def HaveFeatEBEP (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_EBEP)


def HaveStatisticalProfilingFDS (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SPE_FDS)


def HaveFeatHBC (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HBC)


def HaveFeatMOPS (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MOPS)


def HaveFeatTIDCP1 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TIDCP1)


def HaveFeatCMOW (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CMOW)


def HaveMTECanonicalTagCheckingExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE_CANONICAL_TAGS)


def HaveLRCPC3Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LRCPC3)


def HaveMTEStoreOnlyExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE_STORE_ONLY)


def HaveCSSC (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CSSC)


def HaveS1PIExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_S1PIE)


def HaveS1POExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_S1POE)


def HaveS2PIExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_S2PIE)


def HaveS2POExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_S2POE)


def HaveFeatCLRBHB (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CLRBHB)


def HaveTHExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_THE)


def HaveLSE128 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LSE128)


def HaveSysReg128 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SYSREG128)


def HaveSysInstr128 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SYSINSTR128)


def HaveRASv2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_RASv2)


def HaveFeatMEC (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MEC)


def HaveAccessFlagUpdateForTableExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HAFT)


def HaveFeatABLE (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_ABLE)


def DecodeShareability (sh : (BitVec 2)) : SailM Shareability := do
  match sh with
  | 0b10 => (pure (Shareability_OSH))
  | 0b11 => (pure (Shareability_ISH))
  | 0b00 => (pure (Shareability_NSH))
  | _ =>
    (do
      let w__0 ← (( do (ConstrainUnpredictable Unpredictable_Shareability) ) : SailM Constraint )
      match w__0 with
      | .Constraint_OSH => (pure (Shareability_OSH))
      | .Constraint_ISH => (pure (Shareability_ISH))
      | .Constraint_NSH => (pure (Shareability_NSH))
      | _ =>
        (do
          (undefined_Shareability (← occLabel 1210) ())))


def S2DecodeCacheability (attr : (BitVec 2)) : SailM MemAttrHints := do
  let s2attr ← (( do (undefined_MemAttrHints (← occLabel 1214) ()) ) : SailM MemAttrHints )
  let s2attr ← (( do
    match attr with
    | 0b01 =>
      (let s2attr : MemAttrHints := { s2attr with attrs := MemAttr_NC }
      (pure (s2attr)))
    | 0b10 =>
      (let s2attr : MemAttrHints := { s2attr with attrs := MemAttr_WT }
      (pure (s2attr)))
    | 0b11 =>
      (let s2attr : MemAttrHints := { s2attr with attrs := MemAttr_WB }
      (pure (s2attr)))
    | _ =>
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_S2RESMEMATTR) ) : SailM Constraint
          )
        let s2attr : MemAttrHints :=
          match w__0 with
          | .Constraint_NC => { s2attr with attrs := MemAttr_NC }
          | .Constraint_WT => { s2attr with attrs := MemAttr_WT }
          | .Constraint_WB => { s2attr with attrs := MemAttr_WB }
          | _ => s2attr
        (pure (s2attr))) ) : SailM MemAttrHints )
  let w__1 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
  let s2attr := ({ s2attr with hints := w__1 } : MemAttrHints)
  let w__2 ← (( do (__UNKNOWN_boolean ()) ) : SailM Bool )
  let s2attr := ({ s2attr with transient := w__2 } : MemAttrHints)
  (pure (s2attr))


def NormalNCMemAttr (_ : Unit) : SailM MemoryAttributes := do
  let non_cacheable ← (( do (undefined_MemAttrHints (← occLabel 1217) ()) ) : SailM MemAttrHints
    )
  let non_cacheable : MemAttrHints := { non_cacheable with attrs := MemAttr_NC }
  let nc_memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1218) ()) ) : SailM
    MemoryAttributes )
  let nc_memattrs : MemoryAttributes := { nc_memattrs with memtype := MemType_Normal }
  let nc_memattrs : MemoryAttributes := { nc_memattrs with outer := non_cacheable }
  let nc_memattrs : MemoryAttributes := { nc_memattrs with inner := non_cacheable }
  let nc_memattrs : MemoryAttributes := { nc_memattrs with shareability := Shareability_OSH }
  let nc_memattrs : MemoryAttributes := { nc_memattrs with tags := MemTag_Untagged }
  let nc_memattrs : MemoryAttributes := { nc_memattrs with notagaccess := false }
  (pure (nc_memattrs))


/-- Type quantifiers: level : Int -/
def GPCFault (gpf : GPCF) (level : Int) : SailM GPCFRecord := do
  let fault ← (( do (undefined_GPCFRecord (← occLabel 1224) ()) ) : SailM GPCFRecord )
  let fault : GPCFRecord := { fault with gpf := gpf }
  let fault : GPCFRecord := { fault with level := level }
  (pure (fault))


def GPIIndex (pa : (BitVec 56)) : SailM Int := do
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  let w__1 ← (( do (DecodePGS (_get_GPCCR_EL3_Type_PGS w__0)) ) : SailM PGSe )
  let w__2 : Int :=
    match w__1 with
    | .PGS_4KB => (BitVec.toNat (Sail.BitVec.extractLsb pa 15 12))
    | .PGS_16KB => (BitVec.toNat (Sail.BitVec.extractLsb pa 17 14))
    | .PGS_64KB => (BitVec.toNat (Sail.BitVec.extractLsb pa 19 16))
  (pure (w__2))


def GPTLevel0Index (pa : (BitVec 56)) : SailM Int := do
  let pps ← (( do (DecodePPS ()) ) : SailM Int )
  let l0sz ← (( do (GPTL0Size ()) ) : SailM Int )
  if ((pps ≤b l0sz) : Bool)
  then (pure (0))
  else
    (do
      ArmFull.assert ((0 ≤b l0sz) && ((pps -i 1) <b 56)) "sail-arm/v8_base.sail:19758.51-19758.52"
      (pure ((BitVec.toNat
          (Sail.BitVec.extractLsb pa (Sail.Int.toNatChecked ((pps -i 1)))
            (Sail.Int.toNatChecked (l0sz)))))))


def GPTLevel1Index (pa : (BitVec 56)) : SailM Int := do
  let l0sz ← (( do (GPTL0Size ()) ) : SailM Int )
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  let w__1 ← (( do (DecodePGS (_get_GPCCR_EL3_Type_PGS w__0)) ) : SailM PGSe )
  match w__1 with
  | .PGS_4KB =>
    (do
      ArmFull.assert ((16 ≤b (l0sz -i 1)) && ((l0sz -i 1) <b 56)) "sail-arm/v8_base.sail:19768.63-19768.64"
      (pure ((BitVec.toNat (Sail.BitVec.extractLsb pa (Sail.Int.toNatChecked ((l0sz -i 1))) 16)))))
  | .PGS_16KB =>
    (do
      ArmFull.assert ((18 ≤b (l0sz -i 1)) && ((l0sz -i 1) <b 56)) "sail-arm/v8_base.sail:19772.63-19772.64"
      (pure ((BitVec.toNat (Sail.BitVec.extractLsb pa (Sail.Int.toNatChecked ((l0sz -i 1))) 18)))))
  | .PGS_64KB =>
    (do
      ArmFull.assert ((20 ≤b (l0sz -i 1)) && ((l0sz -i 1) <b 56)) "sail-arm/v8_base.sail:19776.63-19776.64"
      (pure ((BitVec.toNat (Sail.BitVec.extractLsb pa (Sail.Int.toNatChecked ((l0sz -i 1))) 20)))))


def __GIC_AcknowledgeInterrupt (_ : Unit) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg __GIC_Pending ) : SailM (Option InterruptID) )
  match w__0 with
  | .some intid =>
    (do
      writeReg __GIC_Pending none
      writeReg __GIC_Active (some intid)
      (pure ((__GIC_InterruptID intid))))
  | none => (pure (GIC_PENDING_NONE))


def StageOA (ia : (BitVec 64)) (d128 : (BitVec 1)) (tgx : TGx) (walkstate : TTWState) : SailM FullAddress := do
  let oa ← (( do (undefined_FullAddress (← occLabel 1246) ()) ) : SailM FullAddress )
  let csize ← (( do (undefined_int_at (← occLabel 1247) ()) ) : SailM Int )
  let tsize : Int := (TranslationSize d128 tgx walkstate.level)
  let csize ← (( do
    if ((walkstate.contiguous == 1#1) : Bool)
    then
      (do
        (ContiguousSize d128 tgx walkstate.level))
    else (pure (0)) ) : SailM Int )
  let csize : Int := csize
  let ia_msb : Int := (tsize +i csize)
  let oa : FullAddress := { oa with paspace := walkstate.baseaddress.paspace }
  ArmFull.assert ((0 ≤b ia_msb) && (ia_msb ≤b 55)) "sail-arm/v8_base.sail:20052.53-20052.54"
  ArmFull.assert (0 ≤b (ia_msb -i 1)) "sail-arm/v8_base.sail:20053.39-20053.40"
  let oa : FullAddress :=
    { oa with address := (Sail.BitVec.castWidth (m := 56) ((Sail.BitVec.extractLsb
          walkstate.baseaddress.address 55 (Sail.Int.toNatChecked (ia_msb))) +++ (Sail.BitVec.extractLsb
          ia (Sail.Int.toNatChecked ((ia_msb -i 1))) 0))) }
  (pure (oa))


def HaveEnhancedPAC (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_EPAC)


def HaveEnhancedPAC2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PAuth2)


def HaveFPAC (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FPAC)


def HaveFPACCombined (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FPACCOMBINE)


def ConstPACField (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CONSTPACFIELD)


def HavePACQARMA3Generic (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACQARMA3)


def HavePACQARMA3Auth (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACQARMA3)


def HavePACQARMA5Generic (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACQARMA5)


def HavePACQARMA5Auth (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACQARMA5)


def HavePACIMPGeneric (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACIMP)


def HavePACIMPAuth (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PACIMP)


def TweakInvShuffle (indata : (BitVec 64)) : SailM (BitVec 64) := do
  let outdata ← (( do (undefined_bitvector_at (← occLabel 1287) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 51 48)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 3 0 w__0) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 7 4 (Sail.BitVec.extractLsb indata 55 52))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 11 8 (Sail.BitVec.extractLsb indata 23 20))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 15 12 (Sail.BitVec.extractLsb indata 27 24))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 19 16 (Sail.BitVec.extractLsb indata 3 0))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 23 20 (Sail.BitVec.extractLsb indata 7 4))
  let w__1 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 11 8)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 27 24 w__1) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 31 28 (Sail.BitVec.extractLsb indata 15 12))
  let w__2 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 31 28)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 35 32 w__2) : (BitVec 64))
  let w__3 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 63 60)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 39 36 w__3) : (BitVec 64))
  let w__4 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 59 56)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 43 40 w__4) : (BitVec 64))
  let w__5 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 19 16)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 47 44 w__5) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 51 48 (Sail.BitVec.extractLsb indata 35 32))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 55 52 (Sail.BitVec.extractLsb indata 39 36))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 59 56 (Sail.BitVec.extractLsb indata 43 40))
  let w__6 ← (( do (TweakCellInvRot (Sail.BitVec.extractLsb indata 47 44)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 63 60 w__6) : (BitVec 64))
  (pure (outdata))


def TweakShuffle (indata : (BitVec 64)) : SailM (BitVec 64) := do
  let outdata ← (( do (undefined_bitvector_at (← occLabel 1289) 64) ) : SailM (BitVec 64) )
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 3 0 (Sail.BitVec.extractLsb indata 19 16))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 7 4 (Sail.BitVec.extractLsb indata 23 20))
  let w__0 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 27 24)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 11 8 w__0) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 15 12 (Sail.BitVec.extractLsb indata 31 28))
  let w__1 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 47 44)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 19 16 w__1) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 23 20 (Sail.BitVec.extractLsb indata 11 8))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 27 24 (Sail.BitVec.extractLsb indata 15 12))
  let w__2 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 35 32)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 31 28 w__2) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 35 32 (Sail.BitVec.extractLsb indata 51 48))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 39 36 (Sail.BitVec.extractLsb indata 55 52))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 43 40 (Sail.BitVec.extractLsb indata 59 56))
  let w__3 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 63 60)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 47 44 w__3) : (BitVec 64))
  let w__4 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 3 0)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 51 48 w__4) : (BitVec 64))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 55 52 (Sail.BitVec.extractLsb indata 7 4))
  let w__5 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 43 40)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 59 56 w__5) : (BitVec 64))
  let w__6 ← (( do (TweakCellRot (Sail.BitVec.extractLsb indata 39 36)) ) : SailM (BitVec 4) )
  let outdata := ((Sail.BitVec.updateSubrange outdata 63 60 w__6) : (BitVec 64))
  (pure (outdata))


def ComputePACIMPDEF (data : (BitVec 64)) (modifier : (BitVec 64)) (key0 : (BitVec 64)) (key1 : (BitVec 64)) : SailM (BitVec 64) := do
  (__UNKNOWN_bits 64)


/-- Type quantifiers: n : Int, width : Nat, List.elem width [8, 16, 32, 64] -/
def X_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:22319.27-22319.28"
  ArmFull.assert ((width == 8) || ((width == 16) || ((width == 32) || (width == 64)))) "sail-arm/v8_base.sail:22320.63-22320.64"
  if ((n != 31) : Bool)
  then
    (do
      let w__0 ← (( do (get_R (Sail.Int.toNatChecked (n))) ) : SailM (BitVec 64) )
      (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
          (Sail.Int.toNatChecked ((width -i 1))) 0)))))
  else (pure ((Sail.BitVec.castWidth (Zeros (n := width)))))


def AArch64_ResetSpecialRegisters (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SP_EL0 w__0
  let w__1 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SP_EL1 w__1
  let w__2 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__2)
  let w__3 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg ELR_EL1 w__3
  if ((HaveEL EL2) : Bool)
  then
    (do
      let w__4 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SP_EL2 w__4
      let w__5 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__5)
      let w__6 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL2 w__6)
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__7 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SP_EL3 w__7
      let w__8 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type w__8)
      let w__9 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL3 w__9)
  else (pure (()))
  if ((HaveAArch32EL EL1) : Bool)
  then
    (do
      let w__10 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
      let w__11 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__10 31 0 w__11)
      let w__12 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
      let w__13 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_irq (Sail.BitVec.updateSubrange w__12 31 0 w__13)
      let w__14 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
      let w__15 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_abt (Sail.BitVec.updateSubrange w__14 31 0 w__15)
      let w__16 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
      let w__17 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_und (Sail.BitVec.updateSubrange w__16 31 0 w__17))
  else (pure (()))
  let w__18 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DLR_EL0 w__18
  let w__19 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__19)


def ELR_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL0) "sail-arm/v8_base.sail:22444.27-22444.28"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  (ELR_read w__1.EL)


def AArch64_RandomTag (_ : Unit) : SailM (BitVec 4) := do
  let tag ← (( do (undefined_bitvector_at (← occLabel 1350) 4) ) : SailM (BitVec 4) )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 3
  (do
    let mut loop_vars := tag
    for i in [loop_i_lower:loop_i_upper:1]i do
      let tag := loop_vars
      loop_vars ← do
        let w__0 ← (( do (AArch64_NextRandomTagBit ()) ) : SailM (BitVec 1) )
        let tag := ((BitVec.update tag (Sail.Int.toNatChecked (i)) (Bit w__0)) : (BitVec 4))
        (pure (tag))
    (pure loop_vars))


def AArch64_ChooseNonExcludedTag (tag_in : (BitVec 4)) (offset_in : (BitVec 4)) (exclude : (BitVec 16)) : SailM (BitVec 4) := do
  let tag : (BitVec 4) := tag_in
  let offset : (BitVec 4) := offset_in
  let w__0 ← (( do
    if ((IsOnes exclude) : Bool)
    then (pure 0b0000#4)
    else
      (do
        let tag ← (( do
          if ((offset == 0b0000#4) : Bool)
          then
            (do
              let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun tag => (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      exclude (BitVec.toNat tag))])) == 1#1))) tag
                fun tag => do (pure ((tag + 0b0001#4) : (BitVec 4)))
              (pure loop_vars))
          else (pure tag) ) : SailM (BitVec 4) )
        let (offset, tag) ← (( do
          let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (offset, tag) => (pure (offset != 0b0000#4))) (offset, tag)
            fun (offset, tag) => do
              let offset : (BitVec 4) := (offset - 0b0001#4)
              let tag : (BitVec 4) := (tag + 0b0001#4)
              let tag ← (( do
                let loop_vars_2 ← sailWhileFuelM (fuel := 1048576) (fun tag => (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        exclude (BitVec.toNat tag))])) == 1#1))) tag
                  fun tag => do (pure ((tag + 0b0001#4) : (BitVec 4)))
                (pure loop_vars_2) ) : SailM (BitVec 4) )
              (pure (offset, tag))
          (pure loop_vars_1) ) : SailM ((BitVec 4) × (BitVec 4)) )
        (pure tag)) ) : SailM (BitVec 4) )
  (pure (w__0))


def PhysMemTagRead (desc : AddressDescriptor) (accdesc : AccessDescriptor) : SailM (PhysMemRetStatus × (BitVec 4)) := do
  let w__0 ← (( do (undefined_PhysMemRetStatus (← occLabel 1354) ()) ) : SailM PhysMemRetStatus
    )
  let w__1 ← (( do (undefined_bitvector_at (← occLabel 1355) 4) ) : SailM (BitVec 4) )
  (pure ((w__0, w__1)))


def __GIC_ClearActiveInterrupt (intid : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg __GIC_Active ) : SailM (Option InterruptID) )
  match w__0 with
  | .some active_intid =>
    (do
      if (((__GIC_InterruptID active_intid) == intid) : Bool)
      then
        (do
          writeReg __GIC_Active none)
      else (pure (())))
  | _ => (pure (()))


def AArch64_S1OverlayPermissions (regime : Regime) (walkstate : TTWState) (accdesc : AccessDescriptor) : SailM S1AccessControls := do
  let r ← (( do (undefined_bitvector_at (← occLabel 1443) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1444) 1) ) : SailM (BitVec 1) )
  let x ← (( do (undefined_bitvector_at (← occLabel 1445) 1) ) : SailM (BitVec 1) )
  let pr ← (( do (undefined_bitvector_at (← occLabel 1446) 1) ) : SailM (BitVec 1) )
  let pw ← (( do (undefined_bitvector_at (← occLabel 1447) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 1448) 1) ) : SailM (BitVec 1) )
  let ur ← (( do (undefined_bitvector_at (← occLabel 1449) 1) ) : SailM (BitVec 1) )
  let uw ← (( do (undefined_bitvector_at (← occLabel 1450) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1451) 1) ) : SailM (BitVec 1) )
  let permissions : Permissions := walkstate.permissions
  let s1overlay_perms ← (( do (undefined_S1AccessControls (← occLabel 1452) ()) ) : SailM
    S1AccessControls )
  let por ← (( do (AArch64_S1POR regime) ) : SailM S1PORType )
  let bit_index : Int := (4 *i (BitVec.toNat permissions.po_index))
  let ppo : (BitVec 4) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb por (Sail.Int.toNatChecked ((bit_index +i 3)))
      (Sail.Int.toNatChecked (bit_index))))
  let (pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    match ppo with
    | 0b0000 =>
      (let (tup__0, tup__1, tup__2) := ((0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0001 =>
      (let (tup__0, tup__1, tup__2) := ((1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0010 =>
      (let (tup__0, tup__1, tup__2) := ((0#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0011 =>
      (let (tup__0, tup__1, tup__2) := ((1#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0100 =>
      (let (tup__0, tup__1, tup__2) := ((0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0101 =>
      (let (tup__0, tup__1, tup__2) := ((1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0110 =>
      (let (tup__0, tup__1, tup__2) := ((0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | 0b0111 =>
      (let (tup__0, tup__1, tup__2) := ((1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
    | b__0 =>
      (let (tup__0, tup__1, tup__2) := ((0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
      let pr : (BitVec 1) := tup__0
      let pw : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      (pr, pw, px))
  let (ur, uw, ux) ← (( do
    if ((HasUnprivileged regime) : Bool)
    then
      (do
        let w__0 ← (( do readReg POR_EL0 ) : SailM (BitVec 64) )
        let upo : (BitVec 4) :=
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((bit_index +i 3))) (Sail.Int.toNatChecked (bit_index))))
        let (ur, uw, ux) : ((BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match upo with
          | 0b0000 =>
            (let (tup__0, tup__1, tup__2) :=
              ((0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0001 =>
            (let (tup__0, tup__1, tup__2) :=
              ((1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0010 =>
            (let (tup__0, tup__1, tup__2) :=
              ((0#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0011 =>
            (let (tup__0, tup__1, tup__2) :=
              ((1#1, 0#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0100 =>
            (let (tup__0, tup__1, tup__2) :=
              ((0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0101 =>
            (let (tup__0, tup__1, tup__2) :=
              ((1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0110 =>
            (let (tup__0, tup__1, tup__2) :=
              ((0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | 0b0111 =>
            (let (tup__0, tup__1, tup__2) :=
              ((1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
          | b__1 =>
            (let (tup__0, tup__1, tup__2) :=
              ((0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
            let ur : (BitVec 1) := tup__0
            let uw : (BitVec 1) := tup__1
            let ux : (BitVec 1) := tup__2
            (ur, uw, ux))
        (pure ((ur, uw, ux))))
    else (pure ((ur, uw, ux))) ) : SailM ((BitVec 1) × (BitVec 1) × (BitVec 1)) )
  let (tup__0, tup__1, tup__2) :=
    (if ((accdesc.el == EL0) : Bool)
    then (ur, uw, ux)
    else (pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
  let r : (BitVec 1) := tup__0
  let w : (BitVec 1) := tup__1
  let x : (BitVec 1) := tup__2
  let s1overlay_perms : S1AccessControls := { s1overlay_perms with or := r }
  let s1overlay_perms : S1AccessControls := { s1overlay_perms with ow := w }
  let s1overlay_perms : S1AccessControls := { s1overlay_perms with ox := x }
  (pure (s1overlay_perms))


end ArmFull.Functions
