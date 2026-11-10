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

def ERXADDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXADDR ) : SailM ERXADDR_Type )
  let w__0 ← (( do readReg ERXADDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXADDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXADDR_Type := value_name
  let w__0 ← (( do readReg ERXADDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERXADDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXADDR r


def ERXMISC0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC0 ) : SailM ERXMISC0_Type )
  let w__0 ← (( do readReg ERXMISC0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXMISC0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC0_Type := value_name
  let w__0 ← (( do readReg ERXMISC0_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC0 r


def ERXMISC5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC5 ) : SailM ERXMISC5_Type )
  let w__0 ← (( do readReg ERXMISC2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXMISC5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC5_Type := value_name
  let w__0 ← (( do readReg ERXMISC2_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC2_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC5 r


def ERXCTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXCTLR2 ) : SailM ERXCTLR2_Type )
  let w__0 ← (( do readReg ERXCTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXCTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXCTLR2_Type := value_name
  let w__0 ← (( do readReg ERXCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ERXCTLR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXCTLR2 r


def ERXMISC1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC1 ) : SailM ERXMISC1_Type )
  let w__0 ← (( do readReg ERXMISC0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXMISC1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC1_Type := value_name
  let w__0 ← (( do readReg ERXMISC0_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC0_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC1 r


def ERXCTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXCTLR ) : SailM ERXCTLR_Type )
  let w__0 ← (( do readReg ERXCTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXCTLR_Type := value_name
  let w__0 ← (( do readReg ERXCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ERXCTLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXCTLR r


def ERXMISC6_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC6 ) : SailM ERXMISC6_Type )
  let w__0 ← (( do readReg ERXMISC3_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXMISC6_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC6_Type := value_name
  let w__0 ← (( do readReg ERXMISC3_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC3_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC6 r


def ERXMISC4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC4 ) : SailM ERXMISC4_Type )
  let w__0 ← (( do readReg ERXMISC2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXMISC4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC4_Type := value_name
  let w__0 ← (( do readReg ERXMISC2_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC4 r


def ERXADDR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXADDR2 ) : SailM ERXADDR2_Type )
  let w__0 ← (( do readReg ERXADDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXADDR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXADDR2_Type := value_name
  let w__0 ← (( do readReg ERXADDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERXADDR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXADDR2 r


def ERXMISC7_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC7 ) : SailM ERXMISC7_Type )
  let w__0 ← (( do readReg ERXMISC3_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXMISC7_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC7_Type := value_name
  let w__0 ← (( do readReg ERXMISC3_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC3_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC7 r


def ERXMISC3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC3 ) : SailM ERXMISC3_Type )
  let w__0 ← (( do readReg ERXMISC1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXMISC3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC3_Type := value_name
  let w__0 ← (( do readReg ERXMISC1_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC1_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC3 r


def ERXSTATUS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXSTATUS ) : SailM ERXSTATUS_Type )
  let w__0 ← (( do readReg ERXSTATUS_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXSTATUS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXSTATUS_Type := value_name
  let w__0 ← (( do readReg ERXSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg ERXSTATUS_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXSTATUS r


def Mk_GICD_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GICD_CTLR_Type_ARE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_GICD_CTLR_Type_ARE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICD_CTLR_Type_ARE_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_GICD_CTLR_Type_ARE_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICD_CTLR_Type_E1NWF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_GICD_CTLR_Type_E1NWF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_GICD_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GICD_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICC_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICV_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICC_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GICV_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_GICD_CTLR_Type_EnableGrp1A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GICD_CTLR_Type_EnableGrp1A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICD_CTLR_Type_RWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_GICD_CTLR_Type_RWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_GICR_CTLR_Type_RWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_GICR_CTLR_Type_RWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_GICD_CTLR_Type_nASSGIreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_GICD_CTLR_Type_nASSGIreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def Mk_GICC_IAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTILAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTILAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_CTILAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_EDLAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_PMLAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_EDLAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_PMLAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def Mk_CTIPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _update_CTIPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_AMPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_EDPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_PMPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _get_AMPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_EDPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_PMPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_CTIPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_CTIPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_AMPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_EDPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_PMPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_AMPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_EDPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_CTIPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_CTIPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_AMDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_AMPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_CTIDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_EDDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_EDPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_AMPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_CTIDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_EDDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_EDPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_CTICIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTICIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_CTICIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_AMCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_EDCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_CTICIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CTICIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_AMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_PMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_AMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_EDCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_PMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_GICH_MISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTIDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CTIDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_AMDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_PMDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_AMDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_EDDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_PMDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_CTIDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_CTIDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_AMDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_EDDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_GITS_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_GITS_CTLR_Type_Enabled (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GITS_CTLR_Type_Enabled (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GITS_CTLR_Type_ITS_Number (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_GITS_CTLR_Type_ITS_Number (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_GITS_CTLR_Type_ImDe (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GITS_CTLR_Type_ImDe (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GITS_CTLR_Type_Quiescent (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_GITS_CTLR_Type_Quiescent (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def Mk_GICR_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)


def _update_EDDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)


def _update_AMDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)


def _update_CTIDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)


def _get_AMDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)


def _get_CTIDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)


def _get_EDDEVARCH_Type_ARCHPART (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)


def _update_EDDEVARCH_Type_ARCHPART (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)


def _get_EDDEVARCH_Type_ARCHVER (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_EDDEVARCH_Type_ARCHVER (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_EDDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_EDDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_AMDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_CTIDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_AMDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_CTIDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def Mk_CTIPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTIPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_CTIPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_AMPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_EDPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_CTIPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CTIPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_AMPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_PMPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_AMPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_EDPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_PMPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_GICV_IAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTSR_Type_DBGH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CNTSR_Type_DBGH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_CNTSR_Type_FCACK (v : (BitVec 32)) : (BitVec 10) :=
  (Sail.BitVec.extractLsb v 17 8)


def _update_CNTSR_Type_FCACK (v : (BitVec 32)) (x : (BitVec 10)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 8 x)


def Mk_EDCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_EDCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_AMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_CTICIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_AMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


end ArmFull.Functions
