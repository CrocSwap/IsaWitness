import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0035
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0053
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0063
import ArmFull.Fn.M0071
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0083
import ArmFull.Fn.M0084

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

def _set_AMIIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMIIDR_Type_ProductID r v)


def _set_GICD_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_IIDR_Type_ProductID r v)


def _set_GICM_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_IIDR_Type_ProductID r v)


def _set_GICR_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_IIDR_Type_ProductID r v)


def _set_GITS_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_IIDR_Type_ProductID r v)


def _set_DBGDEVID1_Type_PCSROffset (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID1_Type_PCSROffset r v)


def _set_EDDEVID1_Type_PCSROffset (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVID1_Type_PCSROffset r v)


def _set_CNTHCTL_Type_PL1PCEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_PL1PCEN r v)


def _set_CNTHCTL_Type_PL1PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_PL1PCTEN r v)


def _set_FPSID_Type_Subarchitecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 7)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_Subarchitecture r v)


def __get_selected_PMEVCNTR (_ : Unit) : SailM (BitVec 32) := do
  let w__0 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  let idx : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__0))
  ArmFull.assert (idx ≤b 30) "sail-arm/v8_base.sail:49451.20-49451.21"
  (PMEVCNTR_read (Sail.Int.toNatChecked (idx)))


def __set_selected_PMEVCNTR (value_name : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  let idx : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__0))
  ArmFull.assert (idx ≤b 30) "sail-arm/v8_base.sail:49459.20-49459.21"
  (PMEVCNTR_set (Sail.Int.toNatChecked (idx)) value_name)


def _set_DBGDTRTXext_Type_DTRTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDTRTXext_Type_DTRTX r v)


def _set_DBGDTRTXint_Type_DTRTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDTRTXint_Type_DTRTX r v)


def _set_DBGOSLAR_Type_OSLA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSLAR_Type_OSLA r v)


def _set_DBGDTRRXext_Type_DTRRX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDTRRXext_Type_DTRRX r v)


def _set_DBGDTRRXint_Type_DTRRX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDTRRXint_Type_DTRRX r v)


def _set_TLBTR_Type_nU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TLBTR_Type_nU r v)


def _set_DBGDEVID_Type_AuxRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_AuxRegs r v)


def _set_EDDEVID_Type_AuxRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVID_Type_AuxRegs r v)


def _set_DBGDEVID_Type_BPAddrMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_BPAddrMask r v)


def _set_DBGDEVID_Type_CIDMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_CIDMask r v)


def _set_DBGDEVID_Type_VectorCatch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_VectorCatch r v)


def _set_DBGDEVID_Type_VirtExtns (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_VirtExtns r v)


def _set_DBGDEVID_Type_WPAddrMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_WPAddrMask r v)


def _set_DBGDIDR_Type_SE_imp (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_SE_imp r v)


def _set_DBGDIDR_Type_Version (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_Version r v)


def _set_DBGDIDR_Type_nSUHD_imp (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_nSUHD_imp r v)


def __set_CNTP_CTL_NS (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  let w__0 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
  (CNTP_CTL_NS_write (Mk_CNTP_CTL_Type (set_slice 2 w__0 0 (BitVec.slice r 0 2))))
  let w__1 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
  (CNTP_CTL_NS_write (Mk_CNTP_CTL_Type (set_slice 29 w__1 3 (BitVec.slice r 3 29))))


def IFAR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFAR_S ) : SailM IFAR_Type )
  if ((HaveEL EL2) : Bool)
  then
    (do
      let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__1 ← (( do (HIFAR_read ()) ) : SailM (BitVec 32) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))


def __get_selected_PMEVTYPER (_ : Unit) : SailM (BitVec 32) := do
  let w__0 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  let idx : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__0))
  ArmFull.assert (idx ≤b 30) "sail-arm/v8_base.sail:51572.20-51572.21"
  (PMEVTYPER_read (Sail.Int.toNatChecked (idx)))


def __set_selected_PMEVTYPER (value_name : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  let idx : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__0))
  ArmFull.assert (idx ≤b 30) "sail-arm/v8_base.sail:51580.20-51580.21"
  (PMEVTYPER_set (Sail.Int.toNatChecked (idx)) value_name)


def __set_CNTV_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTV_CTL_Type := value_name
  let w__0 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTV_CTL_write (Mk_CNTV_CTL_Type (set_slice 2 w__0 0 (BitVec.slice r 0 2))))
  let w__1 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTV_CTL_write (Mk_CNTV_CTL_Type (set_slice 29 w__1 3 (BitVec.slice r 3 29))))


def DFAR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFAR_S ) : SailM DFAR_Type )
  let w__0 ← (( do (HDFAR_read ()) ) : SailM (BitVec 32) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def __set_CNTHP_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHP_CTL_Type := value_name
  let w__0 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHP_CTL_write (Mk_CNTHP_CTL_Type (set_slice 2 w__0 0 (BitVec.slice r 0 2))))
  let w__1 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHP_CTL_write (Mk_CNTHP_CTL_Type (set_slice 29 w__1 3 (BitVec.slice r 3 29))))


def _set_GICD_CTLR_Type_ARE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_ARE r v)


def _set_GICD_CTLR_Type_ARE_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_ARE_S r v)


def _set_GICD_CTLR_Type_E1NWF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_E1NWF r v)


def _set_GICD_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp0 r v)


def _set_GICC_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_CTLR_Type_EnableGrp0 r v)


def _set_GICV_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_CTLR_Type_EnableGrp0 r v)


def _set_GICD_CTLR_Type_EnableGrp1A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1A r v)


def _set_GICD_CTLR_Type_RWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_RWP r v)


def _set_GICR_CTLR_Type_RWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_RWP r v)


def _set_GICD_CTLR_Type_nASSGIreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_nASSGIreq r v)


def _set_CTILAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTILAR_Type_KEY r v)


def _set_EDLAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDLAR_Type_KEY r v)


def _set_PMLAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMLAR_Type_KEY r v)


def _set_CTIPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR2_Type_DES_1 r v)


def _set_AMPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR2_Type_DES_1 r v)


def _set_EDPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR2_Type_DES_1 r v)


def _set_PMPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR2_Type_DES_1 r v)


def _set_CTIPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR2_Type_JEDEC r v)


def _set_AMPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR2_Type_JEDEC r v)


def _set_EDPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR2_Type_JEDEC r v)


def _set_PMPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR2_Type_JEDEC r v)


def _set_CTIPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR2_Type_REVISION r v)


def _set_AMDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVARCH_Type_REVISION r v)


def _set_AMPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR2_Type_REVISION r v)


def _set_CTIDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVARCH_Type_REVISION r v)


def _set_EDDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVARCH_Type_REVISION r v)


def _set_EDPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR2_Type_REVISION r v)


def _set_PMPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR2_Type_REVISION r v)


def _set_CTICIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICIDR1_Type_CLASS r v)


def _set_AMCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR1_Type_CLASS r v)


def _set_EDCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDCIDR1_Type_CLASS r v)


def _set_PMCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCIDR1_Type_CLASS r v)


def _set_CTICIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICIDR1_Type_PRMBL_1 r v)


def _set_AMCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR1_Type_PRMBL_1 r v)


def _set_EDCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDCIDR1_Type_PRMBL_1 r v)


def _set_PMCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCIDR1_Type_PRMBL_1 r v)


def _set_CTIDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVTYPE_Type_MAJOR r v)


def _set_AMDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVTYPE_Type_MAJOR r v)


def _set_EDDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVTYPE_Type_MAJOR r v)


def _set_PMDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMDEVTYPE_Type_MAJOR r v)


def _set_CTIDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVTYPE_Type_SUB r v)


def _set_AMDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVTYPE_Type_SUB r v)


def _set_EDDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVTYPE_Type_SUB r v)


def _set_PMDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMDEVTYPE_Type_SUB r v)


def _set_GITS_CTLR_Type_Enabled (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_CTLR_Type_Enabled r v)


def _set_GITS_CTLR_Type_ITS_Number (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_CTLR_Type_ITS_Number r v)


def _set_GITS_CTLR_Type_ImDe (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_CTLR_Type_ImDe r v)


def _set_GITS_CTLR_Type_Quiescent (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_CTLR_Type_Quiescent r v)


def _set_EDDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHITECT r v)


def _set_AMDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVARCH_Type_ARCHITECT r v)


def _set_CTIDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVARCH_Type_ARCHITECT r v)


def _set_EDDEVARCH_Type_ARCHPART (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHPART r v)


def _set_EDDEVARCH_Type_ARCHVER (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHVER r v)


def _set_EDDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVARCH_Type_PRESENT r v)


def _set_AMDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVARCH_Type_PRESENT r v)


def _set_CTIDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVARCH_Type_PRESENT r v)


def _set_CTIPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR1_Type_DES_0 r v)


def _set_AMPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR1_Type_DES_0 r v)


def _set_EDPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR1_Type_DES_0 r v)


def _set_PMPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR1_Type_DES_0 r v)


def _set_CTIPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR1_Type_PART_1 r v)


def _set_AMPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR1_Type_PART_1 r v)


def _set_EDPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR1_Type_PART_1 r v)


def _set_PMPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR1_Type_PART_1 r v)


def _set_CNTSR_Type_DBGH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTSR_Type_DBGH r v)


def _set_CNTSR_Type_FCACK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 10)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTSR_Type_FCACK r v)


def _set_EDCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDCIDR3_Type_PRMBL_3 r v)


def _set_AMCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR3_Type_PRMBL_3 r v)


def _set_CTICIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICIDR3_Type_PRMBL_3 r v)


def _set_PMCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCIDR3_Type_PRMBL_3 r v)


def _set_GICR_WAKER_Type_ChildrenAsleep (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_WAKER_Type_ChildrenAsleep r v)


def _set_GICR_WAKER_Type_ProcessorSleep (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_WAKER_Type_ProcessorSleep r v)


def _set_GITS_PARTIDR_Type_PARTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_PARTIDR_Type_PARTID r v)


def _set_GICR_PARTIDR_Type_PARTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_PARTIDR_Type_PARTID r v)


def _set_GITS_PARTIDR_Type_PMG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_PARTIDR_Type_PMG r v)


def _set_GICR_PARTIDR_Type_PMG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_PARTIDR_Type_PMG r v)


def _set_CTIPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR0_Type_PART_0 r v)


def _set_AMPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR0_Type_PART_0 r v)


def _set_EDPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR0_Type_PART_0 r v)


def _set_PMPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR0_Type_PART_0 r v)


def _set_EDPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR3_Type_CMOD r v)


def _set_AMPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR3_Type_CMOD r v)


def _set_CTIPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR3_Type_CMOD r v)


def _set_PMPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR3_Type_CMOD r v)


def _set_EDPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR3_Type_REVAND r v)


def _set_AMPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR3_Type_REVAND r v)


def _set_CTIPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR3_Type_REVAND r v)


def _set_PMPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR3_Type_REVAND r v)


def _set_GICC_STATUSR_Type_ASV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_STATUSR_Type_ASV r v)


def _set_GICC_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_STATUSR_Type_RRD r v)


def _set_GICD_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_STATUSR_Type_RRD r v)


def _set_GICR_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_STATUSR_Type_RRD r v)


def _set_GICV_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_STATUSR_Type_RRD r v)


def _set_GITS_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_RRD r v)


def _set_GICC_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_STATUSR_Type_RWOD r v)


def _set_GICD_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_STATUSR_Type_RWOD r v)


def _set_GICR_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_STATUSR_Type_RWOD r v)


def _set_GICV_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_STATUSR_Type_RWOD r v)


def _set_GITS_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_RWOD r v)


def _set_GICC_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_STATUSR_Type_WRD r v)


def _set_GICD_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_STATUSR_Type_WRD r v)


def _set_GICR_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_STATUSR_Type_WRD r v)


def _set_GICV_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_STATUSR_Type_WRD r v)


def _set_GITS_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_WRD r v)


def _set_GICC_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_STATUSR_Type_WROD r v)


def _set_GICD_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_STATUSR_Type_WROD r v)


def _set_GICR_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_STATUSR_Type_WROD r v)


def _set_GICV_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_STATUSR_Type_WROD r v)


end ArmFull.Functions
