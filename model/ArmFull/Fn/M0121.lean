import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0040
import ArmFull.Fn.M0043
import ArmFull.Fn.M0051
import ArmFull.Fn.M0052
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059

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

def SetCurrentGCSPointer (ptr : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  if ((questionMark == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg GCSPR_EL0 ) : SailM (BitVec 64) )
      writeReg GCSPR_EL0 (Sail.BitVec.updateSubrange w__1 63 3 (Sail.BitVec.extractLsb ptr 63 3)))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__2 ← (( do readReg GCSPR_EL1 ) : SailM (BitVec 64) )
          writeReg GCSPR_EL1 (Sail.BitVec.updateSubrange w__2 63 3 (Sail.BitVec.extractLsb ptr 63 3)))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg GCSPR_EL2 ) : SailM (BitVec 64) )
              writeReg GCSPR_EL2 (Sail.BitVec.updateSubrange w__3 63 3
                (Sail.BitVec.extractLsb ptr 63 3)))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
                  writeReg GCSPR_EL3 (Sail.BitVec.updateSubrange w__4 63 3
                    (Sail.BitVec.extractLsb ptr 63 3)))
              else (pure (())))))


def _set_HFGITR_EL2_Type_ATS1E0R (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E0R r v)


def _set_HFGITR_EL2_Type_ATS1E0W (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E0W r v)


def _set_HFGITR_EL2_Type_ATS1E1R (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1R r v)


def _set_HFGITR_EL2_Type_ATS1E1RP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1RP r v)


def _set_HFGITR_EL2_Type_ATS1E1W (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1W r v)


def _set_HFGITR_EL2_Type_ATS1E1WP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1WP r v)


def _set_HFGITR_EL2_Type_CFPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_CFPRCTX r v)


def _set_HFGITR_EL2_Type_COSPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_COSPRCTX r v)


def _set_HFGITR_EL2_Type_CPPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_CPPRCTX r v)


def _set_HFGITR_EL2_Type_DCCISW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCISW r v)


def _set_HFGITR_EL2_Type_DCCIVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCIVAC r v)


def _set_HFGITR_EL2_Type_DCCSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCSW r v)


def _set_HFGITR_EL2_Type_DCCVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAC r v)


def _set_HFGITR_EL2_Type_DCCVADP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVADP r v)


def _set_HFGITR_EL2_Type_DCCVAP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAP r v)


def _set_HFGITR_EL2_Type_DCCVAU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAU r v)


def _set_HFGITR_EL2_Type_DCISW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCISW r v)


def _set_HFGITR_EL2_Type_DCIVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCIVAC r v)


def _set_HFGITR_EL2_Type_DCZVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCZVA r v)


def _set_HFGITR_EL2_Type_DVPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DVPRCTX r v)


def _set_HFGITR_EL2_Type_ERET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ERET r v)


def _set_HFGITR_EL2_Type_ICIALLU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIALLU r v)


def _set_HFGITR_EL2_Type_ICIALLUIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIALLUIS r v)


def _set_HFGITR_EL2_Type_ICIVAU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIVAU r v)


def _set_HFGITR_EL2_Type_SVC_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_SVC_EL0 r v)


def _set_HFGITR_EL2_Type_SVC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_SVC_EL1 r v)


def _set_HFGITR_EL2_Type_TLBIASIDE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1 r v)


def _set_HFGITR_EL2_Type_TLBIASIDE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1IS r v)


def _set_HFGITR_EL2_Type_TLBIASIDE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1OS r v)


def _set_HFGITR_EL2_Type_TLBIRVAAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1 r v)


def _set_HFGITR_EL2_Type_TLBIRVAAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1IS r v)


def _set_HFGITR_EL2_Type_TLBIRVAAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1OS r v)


def _set_HFGITR_EL2_Type_TLBIRVAALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1 r v)


def _set_HFGITR_EL2_Type_TLBIRVAALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1IS r v)


def _set_HFGITR_EL2_Type_TLBIRVAALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1OS r v)


def _set_HFGITR_EL2_Type_TLBIRVAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1 r v)


def _set_HFGITR_EL2_Type_TLBIRVAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1IS r v)


def _set_HFGITR_EL2_Type_TLBIRVAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1OS r v)


def _set_HFGITR_EL2_Type_TLBIRVALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1 r v)


def _set_HFGITR_EL2_Type_TLBIRVALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1IS r v)


def _set_HFGITR_EL2_Type_TLBIRVALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1OS r v)


def _set_HFGITR_EL2_Type_TLBIVAAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1 r v)


def _set_HFGITR_EL2_Type_TLBIVAAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1IS r v)


def _set_HFGITR_EL2_Type_TLBIVAAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1OS r v)


def _set_HFGITR_EL2_Type_TLBIVAALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1 r v)


def _set_HFGITR_EL2_Type_TLBIVAALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1IS r v)


def _set_HFGITR_EL2_Type_TLBIVAALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1OS r v)


def _set_HFGITR_EL2_Type_TLBIVAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1 r v)


def _set_HFGITR_EL2_Type_TLBIVAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1IS r v)


def _set_HFGITR_EL2_Type_TLBIVAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1OS r v)


def _set_HFGITR_EL2_Type_TLBIVALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1 r v)


def _set_HFGITR_EL2_Type_TLBIVALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1IS r v)


def _set_HFGITR_EL2_Type_TLBIVALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1OS r v)


def _set_HFGITR_EL2_Type_TLBIVMALLE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1 r v)


def _set_HFGITR_EL2_Type_TLBIVMALLE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1IS r v)


def _set_HFGITR_EL2_Type_TLBIVMALLE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1OS r v)


def _set_HFGITR_EL2_Type_nBRBIALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nBRBIALL r v)


def _set_HFGITR_EL2_Type_nBRBINJ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nBRBINJ r v)


def _set_HFGITR_EL2_Type_nGCSEPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSEPP r v)


def _set_HFGITR_EL2_Type_nGCSPUSHM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSPUSHM_EL1 r v)


def _set_HFGITR_EL2_Type_nGCSSTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSSTR_EL1 r v)


/-- Type quantifiers: N : Nat, N = 16 -/
def BFZero (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 16) "sail-arm/v8_base.sail:32483.18-32483.19"
  let E : Nat := 8
  let F : Int := (N -i (E +i 1))
  (pure ((Sail.BitVec.castWidth ((sign +++ (Zeros (n := E))) +++ (Zeros
        (n := (Sail.Int.toNatChecked (F))))))))


def AArch64_EncodeAsyncErrorSyndrome (errorstate : ErrorState) : SailM (BitVec 3) := do
  match errorstate with
  | .ErrorState_UC => (pure (0b000#3))
  | .ErrorState_UEU => (pure (0b001#3))
  | .ErrorState_UEO => (pure (0b010#3))
  | .ErrorState_UER => (pure (0b011#3))
  | .ErrorState_CE => (pure (0b110#3))
  | _ =>
    (do
      (Unreachable ())
      (undefined_bitvector_at (← occLabel 1919) 3))


def _set_DISR_EL1_Type_DFSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DISR_EL1_Type_DFSC r v)


def _set_DISR_Type_DFSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DISR_Type_DFSC r v)


def _set_DISR_EL1_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DISR_EL1_Type_IDS r v)


def _set_ID_AA64MMFR2_EL1_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_IDS r v)


def _set_VDISR_EL2_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_IDS r v)


def _set_VSESR_EL2_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSESR_EL2_Type_IDS r v)


def IsSynchronizablePhysicalSErrorPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def _set_RVBAR_EL1_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL1_Type_ResetAddress r v)


def _set_RVBAR_EL2_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL2_Type_ResetAddress r v)


def _set_RVBAR_EL3_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RVBAR_EL3_Type_ResetAddress r v)


def RMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _RMR ) : SailM RMR_Type )
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__1 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))


def RMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : RMR_Type := value_name
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32)))
  else
    (do
      let w__1 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__1 31 0 (BitVec.slice r 0 32)))
  writeReg _RMR r


def SDER_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SDER_Type := value_name
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
      (SDER32_EL3_write (Mk_SDER32_EL3_Type (set_slice 32 w__0 0 (BitVec.slice r 0 32)))))
  else
    (do
      let w__1 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
      writeReg SDER32_EL2 (Sail.BitVec.updateSubrange w__1 31 0 (BitVec.slice r 0 32)))
  writeReg _SDER r


def MPAM3_EL3_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM3_EL3_Type := value_name
  let w__0 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (BitVec.update w__0 63 (Bit (BitVec.slice r 63 1)))
  writeReg _MPAM3_EL3 r


/-- Type quantifiers: k_cold_reset : Bool -/
def ResetExternalDebugRegisters (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__0 0 0 1#1)
  let w__1 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__1 3 3 1#1)
  let w__2 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__2 5 5 1#1)
  if (cold_reset : Bool)
  then
    (do
      let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_STATUS w__3 0b000010#6))
      let w__4 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RW w__4 0b1111#4)))
  else (pure (()))


/-- Type quantifiers: N : Nat, N ≥ 0 -/
def NextInstrAddr (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 64)) "sail-arm/fetch.sail:190.50-190.51"
  let w__0 ← (( do readReg _PC ) : SailM (BitVec 64) )
  let w__1 ← (( do (ThisInstrLength ()) ) : SailM Int )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb (BitVec.addInt w__0 (fdiv_int w__1 8))
      (Sail.Int.toNatChecked ((N -i 1))) 0))))


def _set_HSTR_EL2_Type_T0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T0 r v)


def _set_HSTR_Type_T0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T0 r v)


def _set_HSTR_EL2_Type_T1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T1 r v)


def _set_HSTR_Type_T1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T1 r v)


def _set_HSTR_EL2_Type_T10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T10 r v)


def _set_HSTR_Type_T10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T10 r v)


def _set_HSTR_EL2_Type_T11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T11 r v)


def _set_HSTR_Type_T11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T11 r v)


def _set_HSTR_EL2_Type_T12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T12 r v)


def _set_HSTR_Type_T12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T12 r v)


def _set_HSTR_EL2_Type_T13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T13 r v)


def _set_HSTR_Type_T13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T13 r v)


def _set_HSTR_EL2_Type_T15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T15 r v)


def _set_HSTR_Type_T15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T15 r v)


def _set_HSTR_EL2_Type_T2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T2 r v)


def _set_HSTR_Type_T2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T2 r v)


def _set_HSTR_EL2_Type_T3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T3 r v)


def _set_HSTR_Type_T3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T3 r v)


def _set_HSTR_EL2_Type_T5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T5 r v)


def _set_HSTR_Type_T5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T5 r v)


def _set_HSTR_EL2_Type_T6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T6 r v)


def _set_HSTR_Type_T6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T6 r v)


def _set_HSTR_EL2_Type_T7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T7 r v)


def _set_HSTR_Type_T7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T7 r v)


def _set_HSTR_EL2_Type_T8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T8 r v)


def _set_HSTR_Type_T8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T8 r v)


def _set_HSTR_EL2_Type_T9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HSTR_EL2_Type_T9 r v)


def _set_HSTR_Type_T9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSTR_Type_T9 r v)


def SoftwareStep_DidNotStep (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def SoftwareStep_SteppedEX (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def _set_PMCCNTR_EL0_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCCNTR_EL0_Type_CCNT r v)


def _set_PMCCNTR_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCCNTR_Type_CCNT r v)


def _set_PMCCNTSVR_EL1_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCCNTSVR_EL1_Type_CCNT r v)


/-- Type quantifiers: k_conditional : Bool -/
def SPESampleAddOpOther__1 (conditional : Bool) : SailM Unit := do
  writeReg SPESampleClass 0b00#2
  let w__0 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
  writeReg SPESampleSubclass (BitVec.update w__0 0
    (Bit
      (if (conditional : Bool)
      then 1#1
      else 0#1)))
  writeReg SPESampleOpType OpType_Other


def _set_PMSICR_EL1_Type_COUNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSICR_EL1_Type_COUNT r v)


def _set_PMSICR_EL1_Type_ECOUNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSICR_EL1_Type_ECOUNT r v)


def _set_PMSIRR_EL1_Type_INTERVAL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIRR_EL1_Type_INTERVAL r v)


def _set_PMSIRR_EL1_Type_RND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIRR_EL1_Type_RND r v)


def SPEBufferIsFull (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  let write_pointer_limit : Int :=
    (BitVec.toNat ((_get_PMBLIMITR_EL1_Type_LIMIT w__0) +++ (Zeros (n := 12))))
  let w__1 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
  let current_write_pointer : Int := (BitVec.toNat w__1)
  let w__2 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  let record_max_size : Int := (Int.shiftl 1 (BitVec.toNat (_get_PMSIDR_EL1_Type_MaxSize w__2)))
  (pure ((current_write_pointer >b (write_pointer_limit -i record_max_size))))


def _set_PMSDSFR_EL1_Type_S0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S0 r v)


def _set_ERXGSR_EL1_Type_S0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S0 r v)


def _set_PMSDSFR_EL1_Type_S1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S1 r v)


def _set_ERXGSR_EL1_Type_S1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S1 r v)


def _set_PMSDSFR_EL1_Type_S10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S10 r v)


def _set_ERXGSR_EL1_Type_S10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S10 r v)


def _set_PMSDSFR_EL1_Type_S11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S11 r v)


end ArmFull.Functions
