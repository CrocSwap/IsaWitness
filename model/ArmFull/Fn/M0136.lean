import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0079
import ArmFull.Fn.M0080
import ArmFull.Fn.M0081

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

def _set_ID_AA64SMFR0_EL1_Type_I16I64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_I16I64 r v)


def _set_ID_AA64SMFR0_EL1_Type_I8I32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_I8I32 r v)


def _set_ID_AA64SMFR0_EL1_Type_SMEver (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_SMEver r v)


def __set_MPAM2_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM2_EL2_Type := value_name
  let w__0 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__0 53 0 (BitVec.slice r 0 54))
  let w__1 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1 62 55 (BitVec.slice r 55 8))
  if ((! (HaveEL EL3)) : Bool)
  then
    (do
      let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__2 63 63 (_get_MPAM2_EL2_Type_MPAMEN r)))
  else (pure (()))


def _set_AMEVCNTR1_EL0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR1_EL0_Type_ACNT r v)


def _set_AMEVCNTR0_EL0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR0_EL0_Type_ACNT r v)


def _set_AMEVCNTR0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR0_Type_ACNT r v)


def _set_AMEVCNTR1_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR1_Type_ACNT r v)


def _set_AMCR_EL0_Type_CG1RZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCR_EL0_Type_CG1RZ r v)


def _set_AMCR_Type_CG1RZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCR_Type_CG1RZ r v)


def _set_AMCFGR_EL0_Type_NCG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_NCG r v)


def _set_AMCFGR_Type_NCG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCFGR_Type_NCG r v)


def _set_PMCFGR_Type_NCG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_NCG r v)


def _set_AMCFGR_EL0_Type_SIZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_SIZE r v)


def _set_AMCFGR_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCFGR_Type_SIZE r v)


def _set_AMPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR4_Type_SIZE r v)


def _set_CTIPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR4_Type_SIZE r v)


def _set_EDPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR4_Type_SIZE r v)


def _set_PMCFGR_Type_SIZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_SIZE r v)


def _set_PMPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR4_Type_SIZE r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 r v)


def _set_AMCGCR_EL0_Type_CG0NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_CG0NC r v)


def _set_AMCGCR_Type_CG0NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCGCR_Type_CG0NC r v)


def _set_PMCGCR0_Type_CG0NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCGCR0_Type_CG0NC r v)


def _set_AMCGCR_EL0_Type_CG1NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_CG1NC r v)


def _set_AMCGCR_Type_CG1NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCGCR_Type_CG1NC r v)


def _set_PMCGCR0_Type_CG1NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCGCR0_Type_CG1NC r v)


def _set_ERRIDR_EL1_Type_NUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRIDR_EL1_Type_NUM r v)


def _set_ERRIDR_Type_NUM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ERRIDR_Type_NUM r v)


def __set_BRBSRCINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBSRCINJ_EL1_Type := value_name
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__0) == 0b00#2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__1) == 0b01#2) : Bool)))) ) : SailM Bool )
  if ((! w__2) : Bool)
  then
    (do
      let w__3 ← (( do readReg BRBSRCINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBSRCINJ_EL1 (Sail.BitVec.updateSubrange w__3 63 0
        (_get_BRBSRCINJ_EL1_Type_ADDRESS r)))
  else (pure (()))


def __set_BRBINFINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBINFINJ_EL1_Type := value_name
  let w__0 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__0 4 0 (BitVec.slice r 0 5))
  let w__1 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1 15 14 (BitVec.slice r 14 2))
  let w__2 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__2 31 18 (BitVec.slice r 18 14))
  let w__3 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__3 63 47 (BitVec.slice r 47 17))
  let w__4 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID w__4) == 0b00#2)) : Bool)
  then
    (do
      let w__5 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__5 46 46 (_get_BRBINFINJ_EL1_Type_CCU r)))
  else (pure (()))
  let w__8 ← (( do
    if ((← do
         let w__6 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_BRBINFINJ_EL1_Type_CCU w__6) == 1#1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__7 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__7) == 0b00#2) : Bool)))) ) : SailM Bool )
  if ((! w__8) : Bool)
  then
    (do
      let w__9 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__9 45 32 (_get_BRBINFINJ_EL1_Type_CC r)))
  else (pure (()))
  let w__10 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID w__10) == 0b00#2)) : Bool)
  then
    (do
      let w__11 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__11 17 17
        (_get_BRBINFINJ_EL1_Type_LASTFAILED r)))
  else (pure (()))
  let w__14 ← (( do
    if ((← do
         let w__12 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__12) == 0b00#2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__13 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__13) == 0b01#2) : Bool)))) ) : SailM Bool )
  if ((! w__14) : Bool)
  then
    (do
      let w__15 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__15 16 16 (_get_BRBINFINJ_EL1_Type_T r)))
  else (pure (()))
  let w__16 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID w__16) == 0b00#2)) : Bool)
  then
    (do
      let w__17 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__17 13 8 (_get_BRBINFINJ_EL1_Type_TYPE r)))
  else (pure (()))
  let w__20 ← (( do
    if ((← do
         let w__18 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__18) == 0b00#2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__19 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__19) == 0b10#2) : Bool)))) ) : SailM Bool )
  if ((! w__20) : Bool)
  then
    (do
      let w__21 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__21 7 6 (_get_BRBINFINJ_EL1_Type_EL r)))
  else (pure (()))
  let w__26 ← (( do
    if ((← do
         if ((← do
              let w__22 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__22) == 0b00#2) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__23 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
             (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__23) == 0b01#2) : Bool))))) : Bool)
    then (pure true)
    else
      (do
        let w__25 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                (_get_BRBINFINJ_EL1_Type_TYPE w__25) 5)])) == 1#1) : Bool)))) ) : SailM Bool )
  if ((! w__26) : Bool)
  then
    (do
      let w__27 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__27 5 5 (_get_BRBINFINJ_EL1_Type_MPRED r)))
  else (pure (()))


def __set_BRBTGTINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBTGTINJ_EL1_Type := value_name
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__0) == 0b00#2) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBINFINJ_EL1_Type_VALID w__1) == 0b10#2) : Bool)))) ) : SailM Bool )
  if ((! w__2) : Bool)
  then
    (do
      let w__3 ← (( do readReg BRBTGTINJ_EL1 ) : SailM (BitVec 64) )
      writeReg BRBTGTINJ_EL1 (Sail.BitVec.updateSubrange w__3 63 0
        (_get_BRBTGTINJ_EL1_Type_ADDRESS r)))
  else (pure (()))


def _set_GITS_CREADR_Type_Offset (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CREADR_Type_Offset r v)


def _set_GITS_CWRITER_Type_Offset (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CWRITER_Type_Offset r v)


def _set_GITS_CREADR_Type_Stalled (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CREADR_Type_Stalled r v)


def _set_GICR_PENDBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_InnerCache r v)


def _set_GICR_PROPBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_InnerCache r v)


def _set_GICR_VPENDBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_InnerCache r v)


def _set_GICR_VPROPBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_InnerCache r v)


def _set_GITS_CBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_InnerCache r v)


def _set_GICR_PENDBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_OuterCache r v)


def _set_GICR_PROPBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_OuterCache r v)


def _set_GICR_VPENDBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_OuterCache r v)


def _set_GICR_VPROPBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_OuterCache r v)


def _set_GITS_CBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_OuterCache r v)


def _set_GICR_PENDBASER_Type_PTZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_PTZ r v)


def _set_GICR_PENDBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_Physical_Address r v)


def _set_GICR_PROPBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_Physical_Address r v)


def _set_GICR_VPENDBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Physical_Address r v)


def _set_GICR_VPROPBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Physical_Address r v)


def _set_GITS_CBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_Physical_Address r v)


def _set_GICR_PENDBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_Shareability r v)


def _set_GICR_PROPBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_Shareability r v)


def _set_GICR_VPENDBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Shareability r v)


def _set_GICR_VPROPBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Shareability r v)


def _set_GITS_CBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_Shareability r v)


def _set_GICR_VPROPBASER_Type_Entry_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Entry_Size r v)


def _set_GICR_VPROPBASER_Type_Indirect (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Indirect r v)


def _set_GICR_VPROPBASER_Type_Page_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Page_Size r v)


def _set_GICR_VPROPBASER_Type_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 7)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Size r v)


def _set_GITS_CBASER_Type_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_Size r v)


def _set_GICR_INVALLR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_INVALLR_Type_vPEID r v)


def _set_GICR_INVLPIR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_vPEID r v)


def _set_GICR_VPENDBASER_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_vPEID r v)


def _set_GICR_VSGIR_Type_vPEID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_VSGIR_Type_vPEID r v)


def _set_GITS_SGIR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_SGIR_Type_vPEID r v)


def _set_EDHSR_Type_FnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_FnP r v)


def _set_EDHSR_Type_VNCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_VNCR r v)


def _set_EDHSR_Type_WPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_WPF r v)


def _set_EDHSR_Type_WPT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_WPT r v)


def _set_EDHSR_Type_WPTV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_WPTV r v)


def _set_GICR_VPENDBASER_Type_Dirty (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Dirty r v)


def _set_GICR_VPENDBASER_Type_Doorbell (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Doorbell r v)


def _set_GICR_VPENDBASER_Type_IDAI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_IDAI r v)


def _set_GICR_VPENDBASER_Type_PendingLast (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_PendingLast r v)


def _set_GICR_VPENDBASER_Type_VGrp0En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_VGrp0En r v)


def _set_GICR_VPENDBASER_Type_VGrp1En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_VGrp1En r v)


def _set_GITS_TYPER_Type_CCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_CCT r v)


def _set_GITS_TYPER_Type_CIDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_CIDbits r v)


def _set_GITS_TYPER_Type_CIL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_CIL r v)


def _set_GITS_TYPER_Type_Devbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_Devbits r v)


def _set_GITS_TYPER_Type_HCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_HCC r v)


def _set_GITS_TYPER_Type_ID_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_ID_bits r v)


def _set_GITS_TYPER_Type_INV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_INV r v)


def _set_GITS_TYPER_Type_ITT_entry_size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_ITT_entry_size r v)


def _set_GITS_TYPER_Type_PTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_PTA r v)


def _set_GITS_TYPER_Type_Physical (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_Physical r v)


def _set_GITS_TYPER_Type_SVPET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_SVPET r v)


def _set_GITS_TYPER_Type_UMSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_UMSI r v)


def _set_GITS_STATUSR_Type_UMSI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_UMSI r v)


def _set_GITS_TYPER_Type_UMSIirq (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_UMSIirq r v)


def _set_GITS_CTLR_Type_UMSIirq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_CTLR_Type_UMSIirq r v)


def _set_GITS_TYPER_Type_VMAPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_VMAPP r v)


def _set_GITS_TYPER_Type_VMOVP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_VMOVP r v)


def _set_GITS_TYPER_Type_VSGI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_VSGI r v)


def _set_GITS_TYPER_Type_Virtual (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_Virtual r v)


def _set_GITS_TYPER_Type_nID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_TYPER_Type_nID r v)


def _set_GITS_CWRITER_Type_Retry (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CWRITER_Type_Retry r v)


def _set_EDAA32PFR_Type_MSA_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDAA32PFR_Type_MSA_frac r v)


def _set_PMCFGR_Type_CCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_CCD r v)


def _set_PMCFGR_Type_NA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_NA r v)


def _set_PMIIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMIIDR_Type_ProductID r v)


end ArmFull.Functions
