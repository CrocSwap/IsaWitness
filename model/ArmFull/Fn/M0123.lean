import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0049
import ArmFull.Fn.M0058
import ArmFull.Fn.M0060
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062

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

def _set_PMSEVFR_EL1_Type_E22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E22 r v)


def _set_PMSNEVFR_EL1_Type_E22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E22 r v)


def _set_PMSEVFR_EL1_Type_E23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E23 r v)


def _set_PMSNEVFR_EL1_Type_E23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E23 r v)


def _set_PMSEVFR_EL1_Type_E24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E24 r v)


def _set_PMSNEVFR_EL1_Type_E24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E24 r v)


def _set_PMSEVFR_EL1_Type_E25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E25 r v)


def _set_PMSNEVFR_EL1_Type_E25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E25 r v)


def _set_PMSEVFR_EL1_Type_E26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E26 r v)


def _set_PMSNEVFR_EL1_Type_E26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E26 r v)


def _set_PMSEVFR_EL1_Type_E27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E27 r v)


def _set_PMSNEVFR_EL1_Type_E27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E27 r v)


def _set_PMSEVFR_EL1_Type_E28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E28 r v)


def _set_PMSNEVFR_EL1_Type_E28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E28 r v)


def _set_PMSEVFR_EL1_Type_E29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E29 r v)


def _set_PMSNEVFR_EL1_Type_E29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E29 r v)


def _set_PMSEVFR_EL1_Type_E3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E3 r v)


def _set_EDVIDSR_Type_E3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDVIDSR_Type_E3 r v)


def _set_PMSNEVFR_EL1_Type_E3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E3 r v)


def _set_PMSEVFR_EL1_Type_E30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E30 r v)


def _set_PMSNEVFR_EL1_Type_E30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E30 r v)


def _set_PMSEVFR_EL1_Type_E31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E31 r v)


def _set_PMSNEVFR_EL1_Type_E31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E31 r v)


def _set_PMSEVFR_EL1_Type_E4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E4 r v)


def _set_PMSNEVFR_EL1_Type_E4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E4 r v)


def _set_PMSEVFR_EL1_Type_E48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E48 r v)


def _set_PMSNEVFR_EL1_Type_E48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E48 r v)


def _set_PMSEVFR_EL1_Type_E49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E49 r v)


def _set_PMSNEVFR_EL1_Type_E49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E49 r v)


def _set_PMSEVFR_EL1_Type_E5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E5 r v)


def _set_PMSNEVFR_EL1_Type_E5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E5 r v)


def _set_PMSEVFR_EL1_Type_E50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E50 r v)


def _set_PMSNEVFR_EL1_Type_E50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E50 r v)


def _set_PMSEVFR_EL1_Type_E51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E51 r v)


def _set_PMSNEVFR_EL1_Type_E51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E51 r v)


def _set_PMSEVFR_EL1_Type_E52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E52 r v)


def _set_PMSNEVFR_EL1_Type_E52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E52 r v)


def _set_PMSEVFR_EL1_Type_E53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E53 r v)


def _set_PMSNEVFR_EL1_Type_E53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E53 r v)


def _set_PMSEVFR_EL1_Type_E54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E54 r v)


def _set_PMSNEVFR_EL1_Type_E54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E54 r v)


def _set_PMSEVFR_EL1_Type_E55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E55 r v)


def _set_PMSNEVFR_EL1_Type_E55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E55 r v)


def _set_PMSEVFR_EL1_Type_E56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E56 r v)


def _set_PMSNEVFR_EL1_Type_E56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E56 r v)


def _set_PMSEVFR_EL1_Type_E57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E57 r v)


def _set_PMSNEVFR_EL1_Type_E57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E57 r v)


def _set_PMSEVFR_EL1_Type_E58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E58 r v)


def _set_PMSNEVFR_EL1_Type_E58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E58 r v)


def _set_PMSEVFR_EL1_Type_E59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E59 r v)


def _set_PMSNEVFR_EL1_Type_E59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E59 r v)


def _set_PMSEVFR_EL1_Type_E6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E6 r v)


def _set_PMSNEVFR_EL1_Type_E6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E6 r v)


def _set_PMSEVFR_EL1_Type_E60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E60 r v)


def _set_PMSNEVFR_EL1_Type_E60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E60 r v)


def _set_PMSEVFR_EL1_Type_E61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E61 r v)


def _set_PMSNEVFR_EL1_Type_E61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E61 r v)


def _set_PMSEVFR_EL1_Type_E62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E62 r v)


def _set_PMSNEVFR_EL1_Type_E62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E62 r v)


def _set_PMSEVFR_EL1_Type_E63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E63 r v)


def _set_PMSNEVFR_EL1_Type_E63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E63 r v)


def _set_PMSEVFR_EL1_Type_E7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E7 r v)


def _set_PMSNEVFR_EL1_Type_E7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E7 r v)


def _set_PMSEVFR_EL1_Type_E8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E8 r v)


def _set_PMSNEVFR_EL1_Type_E8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E8 r v)


def _set_PMSEVFR_EL1_Type_E9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E9 r v)


def _set_PMSNEVFR_EL1_Type_E9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E9 r v)


def _set_PMSFCR_EL1_Type_B (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_B r v)


def _set_PMSFCR_EL1_Type_LD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_LD r v)


def _set_LORID_EL1_Type_LD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_LORID_EL1_Type_LD r v)


def _set_PMSLATFR_EL1_Type_MINLAT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSLATFR_EL1_Type_MINLAT r v)


def _set_PMBIDR_EL1_Type_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_Align r v)


def SPEAddByteToRecord (b : (BitVec 8)) : SailM Unit := do
  let size ← (( do readReg SPERecordSize ) : SailM Int )
  ArmFull.assert ((0 ≤b size) && (size <b SPEMaxRecordSize)) "sail-arm/v8_base.sail:35106.46-35106.47"
  let w__0 ← (( do readReg SPERecordData ) : SailM (Vector (BitVec 8) 64) )
  writeReg SPERecordData (vectorUpdate w__0 (Sail.Int.toNatChecked (size)) b)
  writeReg SPERecordSize (size +i 1)


def SPEEmptyRecord (_ : Unit) : SailM Unit := do
  writeReg SPERecordSize 0
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxRecordSize -i 1)))
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg SPERecordData ) : SailM (Vector (BitVec 8) 64) )
        writeReg SPERecordData (vectorUpdate w__0 (Sail.Int.toNatChecked (i)) (Zeros (n := 8)))
    (pure loop_vars))


def SPESampleGeneralPurposeLoadStore (_ : Unit) : SailM Unit := do
  writeReg SPESampleClass 0b01#2
  let w__0 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange w__0 7 1 (Zeros (n := 7)))
  writeReg SPESampleSubclassValid true


def DecodeRegExtend (op : (BitVec 3)) : SailM ExtendType := do
  match op with
  | 0b000 => (pure (ExtendType_UXTB))
  | 0b001 => (pure (ExtendType_UXTH))
  | 0b010 => (pure (ExtendType_UXTW))
  | 0b011 => (pure (ExtendType_UXTX))
  | 0b100 => (pure (ExtendType_SXTB))
  | 0b101 => (pure (ExtendType_SXTH))
  | 0b110 => (pure (ExtendType_SXTW))
  | 0b111 => (pure (ExtendType_SXTX))
  | _ =>
    (do
      (undefined_ExtendType (← occLabel 2456) ()))


def DecodeShift (op : (BitVec 2)) : SailM ShiftType := do
  match op with
  | 0b00 => (pure (ShiftType_LSL))
  | 0b01 => (pure (ShiftType_LSR))
  | 0b10 => (pure (ShiftType_ASR))
  | 0b11 => (pure (ShiftType_ROR))
  | _ =>
    (do
      (undefined_ShiftType (← occLabel 2459) ()))


def Prefetch (address : (BitVec 64)) (prfop : (BitVec 5)) : SailM Unit := SailME.run do
  let hint ← (( do (undefined_PrefetchHint (← occLabel 2460) ()) ) : SailME Unit PrefetchHint )
  let hint ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb prfop 4 3)) with
    | 0b00 => (pure (Prefetch_READ))
    | 0b01 => (pure (Prefetch_EXEC))
    | 0b10 => (pure (Prefetch_WRITE))
    | _ =>
      (do
        SailME.throw (() : Unit)
        (pure (hint))) ) : SailME Unit PrefetchHint )
  let target : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) != 0#1)
  let _ : Unit := (Hint_Prefetch address hint target stream)
  (pure (()))


def TLBI (r : TLBIRecord) (s : Shareability) : SailM Unit := do
  (report_tlbi r s)
  (pure ((_TLBInvalidate ())))


def _set_DCZID_EL0_Type_BS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DCZID_EL0_Type_BS r v)


def _set_GMID_EL1_Type_BS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GMID_EL1_Type_BS r v)


def _set_DCZID_EL0_Type_DZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DCZID_EL0_Type_DZP r v)


def _set_PRRR_Type_DS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_DS0 r v)


def _set_PRRR_Type_DS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_DS1 r v)


def _set_PRRR_Type_NOS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS0 r v)


def _set_PRRR_Type_NOS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS1 r v)


def _set_PRRR_Type_NOS2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS2 r v)


def _set_PRRR_Type_NOS3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS3 r v)


def _set_PRRR_Type_NOS4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS4 r v)


def _set_PRRR_Type_NOS5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS5 r v)


def _set_PRRR_Type_NOS6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS6 r v)


def _set_PRRR_Type_NOS7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NOS7 r v)


def _set_PRRR_Type_NS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NS0 r v)


def _set_CNTNSAR_Type_NS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS0 r v)


def _set_PRRR_Type_NS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_NS1 r v)


def _set_CNTNSAR_Type_NS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS1 r v)


def _set_PRRR_Type_TR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR0 r v)


def _set_PRRR_Type_TR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR1 r v)


def _set_PRRR_Type_TR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR2 r v)


def _set_PRRR_Type_TR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR3 r v)


def _set_PRRR_Type_TR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR4 r v)


def _set_PRRR_Type_TR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR5 r v)


def _set_PRRR_Type_TR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR6 r v)


def _set_PRRR_Type_TR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PRRR_Type_TR7 r v)


def _set_NMRR_Type_IR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR0 r v)


def _set_NMRR_Type_IR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR1 r v)


def _set_NMRR_Type_IR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR2 r v)


def _set_NMRR_Type_IR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR3 r v)


def _set_NMRR_Type_IR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR4 r v)


def _set_NMRR_Type_IR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR5 r v)


def _set_NMRR_Type_IR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR6 r v)


def _set_NMRR_Type_IR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_IR7 r v)


def _set_NMRR_Type_OR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR0 r v)


def _set_NMRR_Type_OR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR1 r v)


def _set_NMRR_Type_OR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR2 r v)


def _set_NMRR_Type_OR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR3 r v)


def _set_NMRR_Type_OR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR4 r v)


def _set_NMRR_Type_OR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR5 r v)


def _set_NMRR_Type_OR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR6 r v)


def _set_NMRR_Type_OR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NMRR_Type_OR7 r v)


/-- Type quantifiers: level : Int -/
def AArch32_DecodeDescriptorTypeLD (descriptor : (BitVec 64)) (level : Int) : DescriptorType :=
  if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb descriptor 1 0)) == 0b11#2) && (level == FINAL_LEVEL)) : Bool)
  then DescriptorType_Leaf
  else
    (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb descriptor 1 0)) == 0b11#2) : Bool)
    then DescriptorType_Table
    else
      (if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb descriptor 1 0)) == 0b01#2) && (level != FINAL_LEVEL)) : Bool)
      then DescriptorType_Leaf
      else DescriptorType_Invalid))


/-- Type quantifiers: index : Int -/
def AArch32_MAIRAttr (index : Int) (mair : (BitVec 64)) : SailM (BitVec 8) := do
  ArmFull.assert (index <b 8) "sail-arm/v8_base.sail:37686.20-37686.21"
  let bit_index : Int := (8 *i index)
  ArmFull.assert ((0 ≤b bit_index) || (! (index <b 8))) "sail-arm/v8_base.sail:37688.58-37688.59"
  (pure ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb mair
      (Sail.Int.toNatChecked ((bit_index +i 7))) (Sail.Int.toNatChecked (bit_index))))))


def AArch32_S2InconsistentSL (walkparams : S2TTWParams) : Bool :=
  let startlevel : Int := (AArch32_S2StartLevel walkparams.sl0)
  let levels : Int := (FINAL_LEVEL -i startlevel)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let stride : Int := (granulebits -i 3)
  let sl_min_iasize : Int := (((levels *i stride) +i granulebits) +i 1)
  let sl_max_iasize : Int := ((sl_min_iasize +i (stride -i 1)) +i 4)
  let iasize : Int := (AArch32_S2IASize walkparams.t0sz)
  ((iasize <b sl_min_iasize) || (iasize >b sl_max_iasize))


def _set_DACR32_EL2_Type_D0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D0 r v)


def _set_DACR_Type_D0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D0 r v)


def _set_DACR32_EL2_Type_D1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D1 r v)


def _set_DACR_Type_D1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D1 r v)


def _set_DACR32_EL2_Type_D10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D10 r v)


def _set_DACR_Type_D10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D10 r v)


def _set_DACR32_EL2_Type_D11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D11 r v)


def _set_DACR_Type_D11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D11 r v)


def _set_DACR32_EL2_Type_D12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D12 r v)


def _set_DACR_Type_D12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D12 r v)


def _set_DACR32_EL2_Type_D13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DACR32_EL2_Type_D13 r v)


def _set_DACR_Type_D13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DACR_Type_D13 r v)


end ArmFull.Functions
