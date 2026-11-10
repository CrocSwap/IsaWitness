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

def _update_SPSR_EL1_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_SPSR_EL2_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_SPSR_EL3_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_SPSR_EL1_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_SPSR_EL2_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_SPSR_EL3_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_DSPSR_EL0_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_DSPSR_EL0_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_SPSR_EL1_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_SPSR_EL2_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_SPSR_EL3_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_SPSR_EL1_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_SPSR_EL2_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_SPSR_EL3_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_DSPSR_EL0_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_DSPSR_EL0_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_DSPSR_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_ID_AA64PFR0_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)


def _update_ID_PFR0_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_PFR0_Type_DIT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_SPSR_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_EL2_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_EL3_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_abt_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_fiq_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_hyp_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_irq_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_mon_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_svc_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SPSR_und_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_DSPSR_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_ID_AA64PFR0_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)


def _get_ID_PFR0_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_PFR0_Type_DIT (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_SPSR_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_EL2_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_EL3_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_abt_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_fiq_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_hyp_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_irq_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_mon_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_svc_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SPSR_und_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_DSPSR_EL0_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _update_DSPSR_EL0_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _update_SPSR_EL1_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _update_SPSR_EL2_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _update_SPSR_EL3_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _get_SPSR_EL1_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _get_SPSR_EL2_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _get_SPSR_EL3_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _get_DSPSR_EL0_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_DSPSR_EL0_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_DBGVCR32_EL2_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_DBGVCR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_DSPSR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ISR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ISR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_PAR_EL1_Type_F (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PAR_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMBIDR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_SPSR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_EL2_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_EL3_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_abt_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_fiq_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_hyp_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_irq_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_mon_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_svc_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SPSR_und_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_DBGVCR32_EL2_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_DBGVCR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_DSPSR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ISR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ISR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_PAR_EL1_Type_F (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PAR_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMBIDR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_SPSR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_EL2_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_EL3_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_abt_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_fiq_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_hyp_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_irq_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_mon_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_svc_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SPSR_und_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_DSPSR_EL0_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_DSPSR_EL0_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_DSPSR_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_EL1_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_EL2_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_EL3_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_abt_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_fiq_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_hyp_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_irq_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_mon_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_svc_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_und_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_DSPSR_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_EL1_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_EL2_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_EL3_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_abt_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_fiq_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_hyp_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_irq_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_mon_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_svc_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_und_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_DSPSR_EL0_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _update_DSPSR_EL0_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_DSPSR_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_EL1_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_EL2_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_EL3_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_abt_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_fiq_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_hyp_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_irq_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_mon_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_svc_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _update_SPSR_und_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((8 -i 1)))
        (Sail.Int.toNatChecked ((((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))))) 26 25
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((8 -i 1) -i ((15 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))))


def _get_DSPSR_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_EL1_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_EL2_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_EL3_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_abt_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_fiq_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_hyp_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_irq_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_mon_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_svc_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_SPSR_und_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))


def _get_DSPSR_EL0_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_DSPSR_EL0_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_DSPSR_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_ID_AA64MMFR1_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_MMFR3_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_MMFR3_Type_PAN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_SPSR_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_EL2_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_EL3_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_abt_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_fiq_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_hyp_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_irq_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_mon_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_svc_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_SPSR_und_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_DSPSR_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_ID_AA64MMFR1_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR3_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_MMFR3_Type_PAN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_SPSR_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_EL2_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_EL3_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_abt_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_fiq_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_hyp_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_irq_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_mon_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_svc_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SPSR_und_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_DSPSR_EL0_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _update_DSPSR_EL0_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _update_SPSR_EL1_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _update_SPSR_EL2_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _update_SPSR_EL3_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _get_SPSR_EL1_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _get_SPSR_EL2_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _get_SPSR_EL3_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _get_DSPSR_EL0_Type_PPEND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _update_DSPSR_EL0_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _update_DSPSR2_Type_PPEND (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_SPSR_EL1_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


end ArmFull.Functions
