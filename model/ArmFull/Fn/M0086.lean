import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def Mk_GICC_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GITS_MPAMIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICD_SGIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICD_SGIR_Type_CPUTargetList (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _update_GICD_SGIR_Type_CPUTargetList (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _get_GICD_SGIR_Type_NSATT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_GICD_SGIR_Type_NSATT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_GICD_SGIR_Type_TargetListFilter (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_GICD_SGIR_Type_TargetListFilter (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def Mk_GICH_VMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_AEOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_AHPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICR_SYNCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_ABPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GITS_MPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICD_SETSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTID_Type_CNTSC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CNTID_Type_CNTSC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def Mk_GITS_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICH_HCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICH_HCR_Type_EOICount (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)


def _update_GICH_HCR_Type_EOICount (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)


def Mk_GICC_BPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIDEVID_Type_EXTMUXNUM (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_CTIDEVID_Type_EXTMUXNUM (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_CTIDEVID_Type_INOUT (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_CTIDEVID_Type_INOUT (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_CTIDEVID_Type_NUMCHAN (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 21 16)


def _update_CTIDEVID_Type_NUMCHAN (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 16 x)


def _get_CTIDEVID_Type_NUMTRIG (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _update_CTIDEVID_Type_NUMTRIG (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def Mk_GICD_SETSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICR_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_EOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTNSAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTNSAR_Type_NS2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_CNTNSAR_Type_NS2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_CNTNSAR_Type_NS3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_CNTNSAR_Type_NS3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_CNTNSAR_Type_NS4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_CNTNSAR_Type_NS4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_CNTNSAR_Type_NS5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_CNTNSAR_Type_NS5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_CNTNSAR_Type_NS6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_CNTNSAR_Type_NS6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_CNTNSAR_Type_NS7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_CNTNSAR_Type_NS7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def Mk_EDITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICD_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_GICC_AIAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMIIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HACTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACTLR2 ) : SailM HACTLR2_Type )
  let w__0 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def HACTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACTLR2_Type := value_name
  let w__0 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
  writeReg ACTLR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _HACTLR2 r


def Mk_PMAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCGCR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def __get_ICC_AP0R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP0R_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_VBAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL2_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 64))))


def __get_HFGITR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGITR2_EL2_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))


def __get_ICV_AP0R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_AP0R_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_VBAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL1_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 64))))


def __get_CNTFRQ_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTFRQ_EL0_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_DBGDTRRX_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDTRRX_EL0_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_OSDTRRX_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSDTRRX_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_OSDTRTX_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSDTRTX_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_VBAR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL3_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
      (Sail.BitVec.zeroExtend 0x7FF#12 64))))


def __get_ID_AA64AFR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64AFR1_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))


def __get_ID_AA64AFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64AFR0_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))


def __get_DBGDSAR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDSAR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))


def __get_JOSCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JOSCR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


def __get_JIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JIDR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


def __get_VBAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 32))))


def __get_VBAR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 32))))


def __get_VBAR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 32))))


def __get_HVBAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HVBAR_Type := value_name
  (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
      (Sail.BitVec.zeroExtend 0x1F#8 32))))


def __get_FCSEIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : FCSEIDR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


def __get_JMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JMCR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


def __get_DBGWFAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWFAR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


def __get_DBGDEVID2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDEVID2_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))


/-- Type quantifiers: Rt : Int, k_acq_rel : Bool, k_sign_extend : Bool, size : Int -/
def AArch32_SetLSInstructionSyndrome (size : Int) (sign_extend : Bool) (Rt : Int) (acq_rel : Bool) : Unit :=
  ()


def BPIALL (_ : Unit) : Unit :=
  ()


def BPIALLIS (_ : Unit) : Unit :=
  ()


def BPIMVA (val_name : (BitVec 32)) : Unit :=
  ()


def CP15DMB (_ : Unit) : Unit :=
  ()


def CP15DSB (_ : Unit) : Unit :=
  ()


def CP15ISB (_ : Unit) : Unit :=
  ()


def CommitTransactionalWrites (_ : Unit) : Unit :=
  ()


def ConstrainUnpredictableProcedure (which : Unpredictable) : Unit :=
  ()


def ConsumptionOfSpeculativeDataBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier_ext (Barrier_CSDB ()))


def DC_CIGDPAPA (val_name : (BitVec 64)) : Unit :=
  ()


def DC_CIPAPA (val_name : (BitVec 64)) : Unit :=
  ()


def Hint_CLRBHB (_ : Unit) : Unit :=
  ()


def Hint_DGH (_ : Unit) : Unit :=
  ()


def Hint_PreloadData (address : (BitVec 32)) : Unit :=
  ()


def Hint_PreloadDataForWrite (address : (BitVec 32)) : Unit :=
  ()


def Hint_PreloadInstr (address : (BitVec 32)) : Unit :=
  ()


/-- Type quantifiers: count : Int, length : Int, reuse : Int, stride : Int -/
def Hint_RangePrefetch (address : (BitVec 64)) (length : Int) (stride : Int) (count : Int) (reuse : Int) (operation : (BitVec 6)) : Unit :=
  ()


def Hint_Yield (_ : Unit) : Unit :=
  ()


def ProfilingSynchronizationBarrier (_ : Unit) : Unit :=
  ()


def SendEvent (_ : Unit) : Unit :=
  ()


def SetIss2 (rs : (BitVec 5)) : Unit :=
  ()


def SetLoadStoreType (instr : (BitVec 2)) : Unit :=
  ()


def SpeculativeStoreBypassBarrierToPA (_ : Unit) : Unit :=
  ()


def SpeculativeStoreBypassBarrierToVA (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_SSBB ()))


def StartTrackingTransactionalReadsWrites (_ : Unit) : Unit :=
  ()


def return_exception (x : (BitVec 56)) : SailM Unit := do
  (sail_return_exception x)


def Init_Devices (_ : Unit) : SailM Unit := do
  writeReg __GIC_Pending none
  writeReg __GIC_Active none


def HaveFP16Ext (_ : Unit) : Bool :=
  true


def ExclusiveMonitorsStatus (_ : Unit) : SailM (BitVec 1) := do
  (undefined_bitvector_at (← occLabel 2887) 1)


/-- Type quantifiers: Rt : Int, k_acq_rel : Bool, k_sign_extend : Bool, k_sixty_four : Bool, size :
  Int -/
def AArch64_SetLSInstructionSyndrome (size : Int) (sign_extend : Bool) (Rt : Int) (sixty_four : Bool) (acq_rel : Bool) : Unit :=
  ()


def DataMemoryBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (sail_barrier
    (Barrier_DMB
      { domain := domain
        types := types
        nXS := false }))


/-- Type quantifiers: k_nXS : Bool -/
def DataSynchronizationBarrier (domain : MBReqDomain) (types : MBReqTypes) (nXS : Bool) : SailM Unit := do
  (sail_barrier
    (Barrier_DSB
      { domain := domain
        types := types
        nXS := nXS }))


def InstructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_ISB ()))


def SpeculationBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_SB ()))


/-- Type quantifiers: t : Int -/
def AArch64_ImpDefSysRegRead (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AArch64_ImpDefSysRegWrite (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: s : Int -/
def SPMCNTENCLR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMCNTENSET_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMCR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: n : Int, s : Int -/
def SPMEVCNTR_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILT2R_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: n : Int, s : Int -/
def SPMEVFILTR_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: n : Int, s : Int -/
def SPMEVTYPER_EL0_set (s : Int) (n : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMINTENCLR_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMINTENSET_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMOVSCLR_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMOVSSET_EL0_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMROOTCR_EL3_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: s : Int -/
def SPMSCR_EL1_set (s : Int) (value_name : (BitVec 64)) : Unit :=
  ()


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_ImpDefSysRegRead128 (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_ImpDefSysRegWrite128 (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: el : Int, t : Int, t2 : Int -/
def AArch64_ImpDefSysInstr128 (el : Int) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (CRm : (BitVec 4)) (op2 : (BitVec 3)) (t : Int) (t2 : Int) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


def execute_aarch32_instrs_DBG_Op_A_txt (_ : Unit) : Unit :=
  ()


def execute_aarch32_instrs_NOP_Op_A_txt (_ : Unit) : Unit :=
  ()


def execute_aarch32_instrs_UDF_Op_A_txt (_ : Unit) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


def execute_aarch64_instrs_integer_flags_axflag (_ : Unit) : SailM Unit := do
  let n : (BitVec 1) := 0#1
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let z : (BitVec 1) := (w__0.Z ||| w__1.V)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let c : (BitVec 1) := (w__2.C &&& (Complement.complement w__3.V))
  let v : (BitVec 1) := 0#1
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with N := n }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with Z := z }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with C := c }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with V := v }


def execute_aarch64_instrs_integer_flags_cfinv (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with C := (Complement.complement w__1.C) }


def execute_aarch64_instrs_udf (_ : Unit) : Unit :=
  ()


def decode_udf_perm_undef_aarch64_instrs_udf (imm16 : (BitVec 16)) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


end ArmFull.Functions
