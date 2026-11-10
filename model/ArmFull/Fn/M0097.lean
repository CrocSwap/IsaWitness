import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0011
import ArmFull.Fn.M0012
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019

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

def _set_SPSR_irq_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_IL r v)


def _set_SPSR_mon_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_IL r v)


def _set_SPSR_svc_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_IL r v)


def _set_SPSR_und_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_IL r v)


def _set_ESRType_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESRType_ISS r v)


def _set_DISR_EL1_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DISR_EL1_Type_ISS r v)


def _set_ESR_EL1_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL1_Type_ISS r v)


def _set_ESR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL2_Type_ISS r v)


def _set_ESR_EL3_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ESR_EL3_Type_ISS r v)


def _set_HSR_Type_ISS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSR_Type_ISS r v)


def _set_VDISR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_ISS r v)


def _set_VSESR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSESR_EL2_Type_ISS r v)


def _set_FPCRType_AH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_AH r v)


def _set_FPCR_Type_AH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_AH r v)


def _set_FPCRType_AHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_AHP r v)


def _set_FPCR_Type_AHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_AHP r v)


def _set_FPSCR_Type_AHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_AHP r v)


def _set_FPCRType_DN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_DN r v)


def _set_FPCR_Type_DN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_DN r v)


def _set_FPSCR_Type_DN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_DN r v)


def _set_FPCRType_DZC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_DZC r v)


def _set_FPSCR_Type_DZC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_DZC r v)


def _set_FPSR_Type_DZC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_DZC r v)


def _set_FPCRType_EBF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_EBF r v)


def _set_FPCR_Type_EBF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_EBF r v)


def _set_FPCRType_FIZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_FIZ r v)


def _set_FPCR_Type_FIZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_FIZ r v)


def _set_FPCRType_FZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_FZ r v)


def _set_FPCR_Type_FZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_FZ r v)


def _set_FPSCR_Type_FZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_FZ r v)


def _set_FPCRType_FZ16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_FZ16 r v)


def _set_FPCR_Type_FZ16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_FZ16 r v)


def _set_FPSCR_Type_FZ16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_FZ16 r v)


def _set_FPCRType_IDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_IDE r v)


def _set_FPCR_Type_IDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_IDE r v)


def _set_FPSCR_Type_IDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IDE r v)


def _set_FPCRType_IOC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_IOC r v)


def _set_FPSCR_Type_IOC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IOC r v)


def _set_FPSR_Type_IOC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_IOC r v)


def _set_FPCRType_IOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_IOE r v)


def _set_FPCR_Type_IOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_IOE r v)


def _set_FPSCR_Type_IOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IOE r v)


def _set_FPCRType_IXE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_IXE r v)


def _set_FPCR_Type_IXE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_IXE r v)


def _set_FPSCR_Type_IXE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IXE r v)


def _set_FPCRType_NEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_NEP r v)


def _set_FPCR_Type_NEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_NEP r v)


def _set_FPCRType_OFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_OFC r v)


def _set_FPSCR_Type_OFC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_OFC r v)


def _set_FPSR_Type_OFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_OFC r v)


def _set_FPCRType_OFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_OFE r v)


def _set_FPCR_Type_OFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_OFE r v)


def _set_FPSCR_Type_OFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_OFE r v)


def _set_FPCRType_RMode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_RMode r v)


def _set_FPCR_Type_RMode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_RMode r v)


def _set_FPSCR_Type_RMode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_RMode r v)


def _set_FPCRType_Stride (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_Stride r v)


def _set_FPCR_Type_Stride (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_Stride r v)


def _set_FPSCR_Type_Stride (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_Stride r v)


def _set_FPCRType_UFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_UFE r v)


def _set_FPCR_Type_UFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_UFE r v)


def _set_FPSCR_Type_UFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_UFE r v)


def _set_FPCRType_length (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCRType_length r v)


def _set_FPCR_Type_length (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPCR_Type_length r v)


def _set_FPSCR_Type_length (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_length r v)


def _set_BRBSRCType_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBSRCType_ADDRESS r v)


def _set_BRBSRCINJ_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBSRCINJ_EL1_Type_ADDRESS r v)


def _set_BRBSRC_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBSRC_EL1_Type_ADDRESS r v)


def _set_BRBTGTINJ_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBTGTINJ_EL1_Type_ADDRESS r v)


def _set_BRBTGTType_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBTGTType_ADDRESS r v)


def _set_BRBTGT_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBTGT_EL1_Type_ADDRESS r v)


def _set_PMIAR_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMIAR_EL1_Type_ADDRESS r v)


def _set_BRBINFType_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_CC r v)


def _set_BRBCR_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_CC r v)


def _set_BRBCR_EL2_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_CC r v)


def _set_BRBIDR0_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_CC r v)


def _set_BRBINFINJ_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_CC r v)


def _set_BRBINF_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_CC r v)


def _set_PMCFGR_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_CC r v)


def _set_BRBINFType_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_CCU r v)


def _set_BRBINFINJ_EL1_Type_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_CCU r v)


def _set_BRBINF_EL1_Type_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_CCU r v)


def _set_BRBINFType_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_EL r v)


def _set_BRBINFINJ_EL1_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_EL r v)


def _set_BRBINF_EL1_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_EL r v)


def _set_EDPCSR_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDPCSR_Type_EL r v)


def _set_EDSCR_Type_EL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_EL r v)


def _set_PMPCSR_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMPCSR_Type_EL r v)


def _set_BRBINFType_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_LASTFAILED r v)


def _set_BRBFCR_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_LASTFAILED r v)


def _set_BRBINFINJ_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_LASTFAILED r v)


def _set_BRBINF_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_LASTFAILED r v)


def _set_BRBINFType_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_MPRED r v)


def _set_BRBCR_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_MPRED r v)


def _set_BRBCR_EL2_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_MPRED r v)


def _set_BRBINFINJ_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_MPRED r v)


def _set_BRBINF_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_MPRED r v)


def _set_BRBINFType_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_T r v)


def _set_BRBINFINJ_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_T r v)


def _set_BRBINF_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_T r v)


def _set_DSPSR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DSPSR_EL0_Type_T r v)


def _set_DSPSR_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DSPSR_Type_T r v)


def _set_PMCCFILTR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_T r v)


def _set_PMEVTYPER_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_T r v)


def _set_PMICFILTR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_T r v)


def _set_PMPCSR_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMPCSR_Type_T r v)


def _set_SPSR_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL1_Type_T r v)


def _set_SPSR_EL2_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL2_Type_T r v)


def _set_SPSR_EL3_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL3_Type_T r v)


def _set_SPSR_abt_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_T r v)


def _set_SPSR_fiq_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_T r v)


def _set_SPSR_hyp_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_T r v)


def _set_SPSR_irq_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_T r v)


def _set_SPSR_mon_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_T r v)


def _set_SPSR_svc_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_T r v)


def _set_SPSR_und_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_T r v)


def _set_BRBINFType_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_TYPE r v)


def _set_BRBINFINJ_EL1_Type_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_TYPE r v)


def _set_BRBINF_EL1_Type_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_TYPE r v)


def _set_BRBINFType_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFType_VALID r v)


def _set_BRBINFINJ_EL1_Type_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_VALID r v)


def _set_BRBINF_EL1_Type_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBINF_EL1_Type_VALID r v)


def undefined_MPAMinfo (ℓ : ChoiceLabel) (_ : Unit) : SailM MPAMinfo := do
  let w__0 ← (( do (undefined_PARTIDspaceType (ℓ.child 0) ()) ) : SailM PARTIDspaceType )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 16) ) : SailM (BitVec 16) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 8) ) : SailM (BitVec 8) )
  (pure ({ mpam_sp := w__0
           partid := w__1
           pmg := w__2 }))


def __UNKNOWN_VARange (_ : Unit) : SailM VARange := do
  (undefined_VARange (← occLabel 79) ())


def __UNKNOWN_Shareability (_ : Unit) : SailM Shareability := do
  (undefined_Shareability (← occLabel 125) ())


def undefined_MemoryAttributes (ℓ : ChoiceLabel) (_ : Unit) : SailM MemoryAttributes := do
  let w__0 ← (( do (undefined_MemType (ℓ.child 0) ()) ) : SailM MemType )
  let w__1 ← (( do (undefined_DeviceType (ℓ.child 1) ()) ) : SailM DeviceType )
  let w__2 ← (( do (undefined_MemAttrHints (ℓ.child 2) ()) ) : SailM MemAttrHints )
  let w__3 ← (( do (undefined_MemAttrHints (ℓ.child 3) ()) ) : SailM MemAttrHints )
  let w__4 ← (( do (undefined_Shareability (ℓ.child 4) ()) ) : SailM Shareability )
  let w__5 ← (( do (undefined_MemTagType (ℓ.child 5) ()) ) : SailM MemTagType )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  (pure ({ memtype := w__0
           device := w__1
           inner := w__2
           outer := w__3
           shareability := w__4
           tags := w__5
           notagaccess := w__6
           xs := w__7 }))


def __UNKNOWN_PASpace (_ : Unit) : SailM PASpace := do
  (undefined_PASpace (← occLabel 137) ())


def undefined_FullAddress (ℓ : ChoiceLabel) (_ : Unit) : SailM FullAddress := do
  let w__0 ← (( do (undefined_PASpace (ℓ.child 0) ()) ) : SailM PASpace )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 56) ) : SailM (BitVec 56) )
  (pure ({ paspace := w__0
           address := w__1 }))


def undefined_GPCFRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM GPCFRecord := do
  let w__0 ← (( do (undefined_GPCF (ℓ.child 0) ()) ) : SailM GPCF )
  let w__1 ← (( do (undefined_int_at (ℓ.child 1) ()) ) : SailM Int )
  (pure ({ gpf := w__0
           level := w__1 }))


def undefined_PhysMemRetStatus (ℓ : ChoiceLabel) (_ : Unit) : SailM PhysMemRetStatus := do
  let w__0 ← (( do (undefined_Fault (ℓ.child 0) ()) ) : SailM Fault )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_ErrorState (ℓ.child 2) ()) ) : SailM ErrorState )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 64) ) : SailM (BitVec 64) )
  (pure ({ statuscode := w__0
           extflag := w__1
           merrorstate := w__2
           store64bstatus := w__3 }))


def __UNKNOWN_Constraint (_ : Unit) : SailM Constraint := do
  (undefined_Constraint (.site 222) ())


def undefined_ExecutionCntxt (ℓ : ChoiceLabel) (_ : Unit) : SailM ExecutionCntxt := do
  let w__0 ← (( do (undefined_bool_at (ℓ.child 0) ()) ) : SailM Bool )
  let w__1 ← (( do (undefined_bool_at (ℓ.child 1) ()) ) : SailM Bool )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 16) ) : SailM (BitVec 16) )
  let w__3 ← (( do (undefined_bool_at (ℓ.child 3) ()) ) : SailM Bool )
  let w__4 ← (( do (undefined_bool_at (ℓ.child 4) ()) ) : SailM Bool )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 16) ) : SailM (BitVec 16) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 2) ) : SailM (BitVec 2) )
  let w__7 ← (( do (undefined_SecurityState (ℓ.child 7) ()) ) : SailM SecurityState )
  let w__8 ← (( do (undefined_RestrictType (ℓ.child 8) ()) ) : SailM RestrictType )
  (pure ({ is_vmid_valid := w__0
           all_vmid := w__1
           vmid := w__2
           is_asid_valid := w__3
           all_asid := w__4
           asid := w__5
           target_el := w__6
           security := w__7
           restriction := w__8 }))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def get_R (n : Nat) : SailM (BitVec 64) := do
  (read_gpr n)


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def set_R (n : Nat) (v : (BitVec 64)) : SailM Unit := do
  (write_gpr n v)


/-- Type quantifiers: n : Nat, lo : Nat, hi : Nat, 0 ≤ n ∧ n ≤ 30 ∧
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 63 -/
def set_R_bits (n : Nat) (hi : Nat) (lo : Nat) (v : (BitVec (hi - lo + 1))) : SailM Unit := do
  (write_gpr_bits n hi lo (Sail.BitVec.castWidth v))


/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def ignore_dependency_edge (n : Nat) (m : Nat) : Unit :=
  if (((n ≤b 30) && (m ≤b 30)) : Bool)
  then (sail_mark_register_pair (register_ref n) (register_ref m) "ignore_edge")
  else ()


def DefaultPARTID : PARTIDtype := (integer_subrange 0 15 0)


def DefaultPMG : PMGtype := (integer_subrange 0 7 0)


def __UNKNOWN_SDFType (_ : Unit) : SailM SDFType := do
  (undefined_SDFType (← occLabel 273) ())


def undefined_S1TTWParams (ℓ : ChoiceLabel) (_ : Unit) : SailM S1TTWParams := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_MAIRType (ℓ.child 8) ()) ) : SailM (BitVec 64) )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 1) ) : SailM (BitVec 1) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 3) ) : SailM (BitVec 3) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 6) ) : SailM (BitVec 6) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 12) 1) ) : SailM (BitVec 1) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 1) ) : SailM (BitVec 1) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 15) 1) ) : SailM (BitVec 1) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 17) 1) ) : SailM (BitVec 1) )
  let w__18 ← (( do (undefined_bitvector_at (ℓ.child 18) 1) ) : SailM (BitVec 1) )
  let w__19 ← (( do (undefined_bitvector_at (ℓ.child 19) 1) ) : SailM (BitVec 1) )
  let w__20 ← (( do (undefined_bitvector_at (ℓ.child 20) 2) ) : SailM (BitVec 2) )
  let w__21 ← (( do (undefined_bitvector_at (ℓ.child 21) 1) ) : SailM (BitVec 1) )
  let w__22 ← (( do (undefined_S1PIRType (ℓ.child 22) ()) ) : SailM (BitVec 64) )
  let w__23 ← (( do (undefined_S1PIRType (ℓ.child 23) ()) ) : SailM (BitVec 64) )
  let w__24 ← (( do (undefined_bitvector_at (ℓ.child 24) 1) ) : SailM (BitVec 1) )
  let w__25 ← (( do (undefined_bitvector_at (ℓ.child 25) 1) ) : SailM (BitVec 1) )
  let w__26 ← (( do (undefined_bitvector_at (ℓ.child 26) 3) ) : SailM (BitVec 3) )
  let w__27 ← (( do (undefined_bitvector_at (ℓ.child 27) 3) ) : SailM (BitVec 3) )
  let w__28 ← (( do (undefined_bitvector_at (ℓ.child 28) 1) ) : SailM (BitVec 1) )
  let w__29 ← (( do (undefined_TGx (ℓ.child 29) ()) ) : SailM TGx )
  let w__30 ← (( do (undefined_bitvector_at (ℓ.child 30) 2) ) : SailM (BitVec 2) )
  let w__31 ← (( do (undefined_bitvector_at (ℓ.child 31) 2) ) : SailM (BitVec 2) )
  let w__32 ← (( do (undefined_bitvector_at (ℓ.child 32) 2) ) : SailM (BitVec 2) )
  let w__33 ← (( do (undefined_bitvector_at (ℓ.child 33) 1) ) : SailM (BitVec 1) )
  let w__34 ← (( do (undefined_bitvector_at (ℓ.child 34) 1) ) : SailM (BitVec 1) )
  let w__35 ← (( do (undefined_bitvector_at (ℓ.child 35) 1) ) : SailM (BitVec 1) )
  let w__36 ← (( do (undefined_bitvector_at (ℓ.child 36) 1) ) : SailM (BitVec 1) )
  let w__37 ← (( do (undefined_bitvector_at (ℓ.child 37) 1) ) : SailM (BitVec 1) )
  let w__38 ← (( do (undefined_bitvector_at (ℓ.child 38) 1) ) : SailM (BitVec 1) )
  let w__39 ← (( do (undefined_MAIRType (ℓ.child 39) ()) ) : SailM (BitVec 64) )
  (pure ({ ha := w__0
           hd := w__1
           tbi := w__2
           tbid := w__3
           nfd := w__4
           e0pd := w__5
           d128 := w__6
           aie := w__7
           mair2 := w__8
           ds := w__9
           ps := w__10
           txsz := w__11
           epan := w__12
           dct := w__13
           nv1 := w__14
           cmow := w__15
           pnch := w__16
           disch := w__17
           haft := w__18
           mtx := w__19
           skl := w__20
           pie := w__21
           pir := w__22
           pire0 := w__23
           emec := w__24
           amec := w__25
           t0sz := w__26
           t1sz := w__27
           uwxn := w__28
           tgx := w__29
           irgn := w__30
           orgn := w__31
           sh := w__32
           hpd := w__33
           ee := w__34
           wxn := w__35
           ntlsmd := w__36
           dc := w__37
           sif := w__38
           mair := w__39 }))


end ArmFull.Functions
