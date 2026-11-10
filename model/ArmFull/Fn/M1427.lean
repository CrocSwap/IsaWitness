import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1060
import ArmFull.Fn.M1061
import ArmFull.Fn.M1109
import ArmFull.Fn.M1300
import ArmFull.Fn.M1301
import ArmFull.Fn.M1302

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64_LoadStore__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__261 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
             __opcode 29 10)) == (0x66002#20 : (BitVec 20)))) : Bool) : Bool)
    then
      (do
        let w__260 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__260 <b 576) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__261 : Bool)
  then
    (do
      writeReg SEE 576
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let size := (BitVec.slice __opcode 30 2)
      (decode_stlr_aarch64_instrs_memory_ordered_writeback Rt Rn size)
      (pure false))
  else
    (do
      let w__263 ← (( do
        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0000100010011111111111#22 : (BitVec 22))) : Bool) : Bool)
        then
          (do
            let w__262 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__262 <b 577) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__263 : Bool)
      then
        (do
          writeReg SEE 577
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let Rt2 := (BitVec.slice __opcode 10 5)
          let o0 := (BitVec.slice __opcode 15 1)
          let Rs := (BitVec.slice __opcode 16 5)
          let L := (BitVec.slice __opcode 22 1)
          let size := (BitVec.slice __opcode 30 2)
          if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 20)])) != 1#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size))
          (pure false))
      else
        (do
          let w__265 ← (( do
            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0100100010011111111111#22 : (BitVec 22))) : Bool) : Bool)
            then
              (do
                let w__264 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__264 <b 578) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__265 : Bool)
          then
            (do
              writeReg SEE 578
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let Rt2 := (BitVec.slice __opcode 10 5)
              let o0 := (BitVec.slice __opcode 15 1)
              let Rs := (BitVec.slice __opcode 16 5)
              let L := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 30 2)
              if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 20)])) != 1#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size))
              (pure false))
          else
            (do
              let w__267 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                         __opcode 29 15)) == (0b001000011111111#15 : (BitVec 15)))) : Bool) : Bool)
                then
                  (do
                    let w__266 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__266 <b 579) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__267 : Bool)
              then
                (do
                  writeReg SEE 579
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rt2 := (BitVec.slice __opcode 10 5)
                  let o0 := (BitVec.slice __opcode 15 1)
                  let Rs := (BitVec.slice __opcode 16 5)
                  let L := (BitVec.slice __opcode 22 1)
                  let sz := (BitVec.slice __opcode 30 1)
                  if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 20)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz))
                  (pure false))
              else
                (do
                  let w__269 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                             __opcode 29 15)) == (0b001000011111110#15 : (BitVec 15)))) : Bool) : Bool)
                    then
                      (do
                        let w__268 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__268 <b 580) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__269 : Bool)
                  then
                    (do
                      writeReg SEE 580
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rt2 := (BitVec.slice __opcode 10 5)
                      let o0 := (BitVec.slice __opcode 15 1)
                      let Rs := (BitVec.slice __opcode 16 5)
                      let L := (BitVec.slice __opcode 22 1)
                      let sz := (BitVec.slice __opcode 30 1)
                      if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 20)])) != 1#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_ldxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz))
                      (pure false))
                  else
                    (do
                      let w__271 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                   __opcode 29 21)) == (0b001000001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 15 15)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__270 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__270 <b 581) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__271 : Bool)
                      then
                        (do
                          writeReg SEE 581
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Rt2 := (BitVec.slice __opcode 10 5)
                          let o0 := (BitVec.slice __opcode 15 1)
                          let Rs := (BitVec.slice __opcode 16 5)
                          let L := (BitVec.slice __opcode 22 1)
                          let sz := (BitVec.slice __opcode 30 1)
                          (decode_stlxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz)
                          (pure false))
                      else
                        (do
                          let w__273 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                       __opcode 29 21)) == (0b001000001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__272 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__272 <b 582) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__273 : Bool)
                          then
                            (do
                              writeReg SEE 582
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Rt2 := (BitVec.slice __opcode 10 5)
                              let o0 := (BitVec.slice __opcode 15 1)
                              let Rs := (BitVec.slice __opcode 16 5)
                              let L := (BitVec.slice __opcode 22 1)
                              let sz := (BitVec.slice __opcode 30 1)
                              (decode_stxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz)
                              (pure false))
                          else
                            (do
                              let w__275 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                         __opcode 29 10)) == (0x217FF#20 : (BitVec 20)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__274 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__274 <b 583) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__275 : Bool)
                              then
                                (do
                                  writeReg SEE 583
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Rt2 := (BitVec.slice __opcode 10 5)
                                  let o0 := (BitVec.slice __opcode 15 1)
                                  let Rs := (BitVec.slice __opcode 16 5)
                                  let L := (BitVec.slice __opcode 22 1)
                                  let size := (BitVec.slice __opcode 30 2)
                                  if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 20)])) != 1#1)) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2
                                        o0 Rs L size))
                                  (pure false))
                              else
                                (do
                                  let w__277 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                           __opcode 31 10)) == (0b0000100001011111111111#22 : (BitVec 22))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__276 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__276 <b 584) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__277 : Bool)
                                  then
                                    (do
                                      writeReg SEE 584
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Rt2 := (BitVec.slice __opcode 10 5)
                                      let o0 := (BitVec.slice __opcode 15 1)
                                      let Rs := (BitVec.slice __opcode 16 5)
                                      let L := (BitVec.slice __opcode 22 1)
                                      let size := (BitVec.slice __opcode 30 2)
                                      if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 20)])) != 1#1)) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt
                                            Rn Rt2 o0 Rs L size))
                                      (pure false))
                                  else
                                    (do
                                      let w__279 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                               __opcode 31 10)) == (0b0100100001011111111111#22 : (BitVec 22))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__278 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__278 <b 585) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__279 : Bool)
                                      then
                                        (do
                                          writeReg SEE 585
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Rt2 := (BitVec.slice __opcode 10 5)
                                          let o0 := (BitVec.slice __opcode 15 1)
                                          let Rs := (BitVec.slice __opcode 16 5)
                                          let L := (BitVec.slice __opcode 22 1)
                                          let size := (BitVec.slice __opcode 30 2)
                                          if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 20)])) != 1#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_ldaxrh_aarch64_instrs_memory_exclusive_single
                                                Rt Rn Rt2 o0 Rs L size))
                                          (pure false))
                                      else
                                        (do
                                          let w__281 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                     __opcode 29 10)) == (0x217DF#20 : (BitVec 20)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__280 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__280 <b 586) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__281 : Bool)
                                          then
                                            (do
                                              writeReg SEE 586
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Rt2 := (BitVec.slice __opcode 10 5)
                                              let o0 := (BitVec.slice __opcode 15 1)
                                              let Rs := (BitVec.slice __opcode 16 5)
                                              let L := (BitVec.slice __opcode 22 1)
                                              let size := (BitVec.slice __opcode 30 2)
                                              if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 20)])) != 1#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_ldxr_aarch64_instrs_memory_exclusive_single
                                                    Rt Rn Rt2 o0 Rs L size))
                                              (pure false))
                                          else
                                            (do
                                              let w__283 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                       __opcode 31 10)) == (0b0000100001011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__282 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__282 <b 587) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__283 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 587
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Rt2 := (BitVec.slice __opcode 10 5)
                                                  let o0 := (BitVec.slice __opcode 15 1)
                                                  let Rs := (BitVec.slice __opcode 16 5)
                                                  let L := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 30 2)
                                                  if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 20)])) != 1#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_ldxrb_aarch64_instrs_memory_exclusive_single
                                                        Rt Rn Rt2 o0 Rs L size))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__285 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                           __opcode 31 10)) == (0b0100100001011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__284 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__284 <b 588) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__285 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 588
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Rt2 := (BitVec.slice __opcode 10 5)
                                                      let o0 := (BitVec.slice __opcode 15 1)
                                                      let Rs := (BitVec.slice __opcode 16 5)
                                                      let L := (BitVec.slice __opcode 22 1)
                                                      let size := (BitVec.slice __opcode 30 2)
                                                      if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 20)])) != 1#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_ldxrh_aarch64_instrs_memory_exclusive_single
                                                            Rt Rn Rt2 o0 Rs L size))
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__287 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                   __opcode 29 21)) == (0b001000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b111111#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__286 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__286 <b 589) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__287 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 589
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Rt2 := (BitVec.slice __opcode 10 5)
                                                          let o0 := (BitVec.slice __opcode 15 1)
                                                          let Rs := (BitVec.slice __opcode 16 5)
                                                          let L := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 30 2)
                                                          if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 14)])) != 1#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_stlxr_aarch64_instrs_memory_exclusive_single
                                                                Rt Rn Rt2 o0 Rs L size))
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__289 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b00001000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__288 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__288 <b 590) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__289 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 590
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Rt2 :=
                                                                (BitVec.slice __opcode 10 5)
                                                              let o0 := (BitVec.slice __opcode 15 1)
                                                              let Rs := (BitVec.slice __opcode 16 5)
                                                              let L := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 30 2)
                                                              if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 14)])) != 1#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_stlxrb_aarch64_instrs_memory_exclusive_single
                                                                    Rt Rn Rt2 o0 Rs L size))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__291 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01001000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__290 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__290 <b 591) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__291 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 591
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Rt2 :=
                                                                    (BitVec.slice __opcode 10 5)
                                                                  let o0 :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let L :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 14)])) != 1#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_stlxrh_aarch64_instrs_memory_exclusive_single
                                                                        Rt Rn Rt2 o0 Rs L size))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__293 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                               __opcode 29 21)) == (0b001000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b011111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__292 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__292 <b 592) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__293 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 592
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Rt2 :=
                                                                        (BitVec.slice __opcode 10 5)
                                                                      let o0 :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let L :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 14)])) != 1#1)) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_stxr_aarch64_instrs_memory_exclusive_single
                                                                            Rt Rn Rt2 o0 Rs L size))
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__295 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b00001000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b011111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__294 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__294 <b 593) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__295 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 593
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Rt2 :=
                                                                            (BitVec.slice __opcode
                                                                              10 5)
                                                                          let o0 :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let L :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 14)])) != 1#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_stxrb_aarch64_instrs_memory_exclusive_single
                                                                                Rt Rn Rt2 o0 Rs L
                                                                                size))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__297 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b01001000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b011111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__296 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__296 <b 594) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__297 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 594
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rt2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 5)
                                                                              let o0 :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 14)])) != 1#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_stxrh_aarch64_instrs_memory_exclusive_single
                                                                                    Rt Rn Rt2 o0 Rs
                                                                                    L size))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__299 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__298 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__298 <b 595) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__299 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 595
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 3)
                                                                                  let o3 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 15 1)
                                                                                  let Rt2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let R :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let A :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp
                                                                                    Rt Rn opc o3 Rt2
                                                                                    R A S)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__301 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b11011001011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__300 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__300 <b 596) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__301 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 596
                                                                                      let Xt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Xn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let imm9 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 9)
                                                                                      (decode_ldg_aarch64_instrs_integer_tags_mcgettag
                                                                                        Xt Xn imm9)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__303 ← (( do
                                                                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               31 10)) == (0b1101100111100000000000#22 : (BitVec 22))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__302 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__302 <b 597) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__303 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 597
                                                                                          let Xt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Xn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          (decode_ldgm_aarch64_instrs_integer_tags_mcgettagarray
                                                                                            Xt Xn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__305 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       29
                                                                                                       21)) == (0b011001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         10)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__304 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__304 <b 598) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__305 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 598
                                                                                              let Rt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let opc2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Rt2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let L :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_ldiapp_aarch64_instrs_memory_ordered_pair_ldiapp
                                                                                                Rt
                                                                                                Rn
                                                                                                opc2
                                                                                                Rt2
                                                                                                L
                                                                                                size)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__307 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       30
                                                                                                       22)) == (0b010100001#9 : (BitVec 9))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__306 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__306 <b 599) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__307 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 599
                                                                                                  let Rt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Rt2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      5)
                                                                                                  let imm7 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      15
                                                                                                      7)
                                                                                                  let L :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let opc :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc
                                                                                                    Rt
                                                                                                    Rn
                                                                                                    Rt2
                                                                                                    imm7
                                                                                                    L
                                                                                                    opc)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__309 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           30
                                                                                                           22)) == (0b010100000#9 : (BitVec 9))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__308 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__308 <b 600) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__309 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 600
                                                                                                      let Rt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Rt2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          5)
                                                                                                      let imm7 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          15
                                                                                                          7)
                                                                                                      let L :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let opc :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc
                                                                                                        Rt
                                                                                                        Rn
                                                                                                        Rt2
                                                                                                        imm7
                                                                                                        L
                                                                                                        opc)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__311 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               22)) == (0xB1#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__310 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__310 <b 601) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__311 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 601
                                                                                                          let Rt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Rt2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              5)
                                                                                                          let imm7 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              15
                                                                                                              7)
                                                                                                          let L :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let opc :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc
                                                                                                            Rt
                                                                                                            Rn
                                                                                                            Rt2
                                                                                                            imm7
                                                                                                            L
                                                                                                            opc)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (pure true))))))))))))))))))))))))))


end ArmFull.Functions
