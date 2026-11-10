import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0992
import ArmFull.Fn.M0993
import ArmFull.Fn.M0994

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
def __DecodeA64_SME__seg10 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__727 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 4 2)) == (0b000#3 : (BitVec 3))))))) : Bool) : Bool)
    then
      (do
        let w__726 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__726 <b 2557) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__727 : Bool)
  then
    (do
      writeReg SEE 2557
      let sz := (BitVec.slice __opcode 22 1)
      let Zm := (BitVec.slice __opcode 16 4)
      let Rv := (BitVec.slice __opcode 13 2)
      let Zn := (BitVec.slice __opcode 5 5)
      let U := (BitVec.slice __opcode 4 1)
      let S := (BitVec.slice __opcode 3 1)
      let off2 := (BitVec.slice __opcode 0 2)
      (decode_SMLALL_ZA_ZZV_1 sz Zm Rv Zn U S off2)
      (pure false))
  else
    (do
      let w__729 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 4 2)) == (0b010#3 : (BitVec 3))))))) : Bool) : Bool)
        then
          (do
            let w__728 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__728 <b 2558) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__729 : Bool)
      then
        (do
          writeReg SEE 2558
          let sz := (BitVec.slice __opcode 22 1)
          let Zm := (BitVec.slice __opcode 16 4)
          let Rv := (BitVec.slice __opcode 13 2)
          let Zn := (BitVec.slice __opcode 5 5)
          let U := (BitVec.slice __opcode 4 1)
          let S := (BitVec.slice __opcode 3 1)
          let off2 := (BitVec.slice __opcode 0 2)
          (decode_SMLSLL_ZA_ZZV_1 sz Zm Rv Zn U S off2)
          (pure false))
      else
        (do
          let w__731 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 4 2)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
            then
              (do
                let w__730 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__730 <b 2559) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__731 : Bool)
          then
            (do
              writeReg SEE 2559
              let sz := (BitVec.slice __opcode 22 1)
              let Zm := (BitVec.slice __opcode 16 4)
              let Rv := (BitVec.slice __opcode 13 2)
              let Zn := (BitVec.slice __opcode 5 5)
              let U := (BitVec.slice __opcode 4 1)
              let S := (BitVec.slice __opcode 3 1)
              let off2 := (BitVec.slice __opcode 0 2)
              (decode_USMLALL_ZA_ZZV_S sz Zm Rv Zn U S off2)
              (pure false))
          else
            (do
              let w__733 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                               __opcode 5 1)) == (0b01000#5 : (BitVec 5))))))) : Bool) : Bool)
                then
                  (do
                    let w__732 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__732 <b 2560) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__733 : Bool)
              then
                (do
                  writeReg SEE 2560
                  let sz := (BitVec.slice __opcode 22 1)
                  let Zm := (BitVec.slice __opcode 17 4)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let Zn := (BitVec.slice __opcode 6 4)
                  let U := (BitVec.slice __opcode 4 1)
                  let S := (BitVec.slice __opcode 3 1)
                  let o1 := (BitVec.slice __opcode 0 1)
                  (decode_UMLALL_ZA_ZZW_2x2 sz Zm Rv Zn U S o1)
                  (pure false))
              else
                (do
                  let w__735 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 5 1)) == (0b01100#5 : (BitVec 5))))))) : Bool) : Bool)
                    then
                      (do
                        let w__734 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__734 <b 2561) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__735 : Bool)
                  then
                    (do
                      writeReg SEE 2561
                      let sz := (BitVec.slice __opcode 22 1)
                      let Zm := (BitVec.slice __opcode 17 4)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let Zn := (BitVec.slice __opcode 6 4)
                      let U := (BitVec.slice __opcode 4 1)
                      let S := (BitVec.slice __opcode 3 1)
                      let o1 := (BitVec.slice __opcode 0 1)
                      (decode_UMLSLL_ZA_ZZW_2x2 sz Zm Rv Zn U S o1)
                      (pure false))
                  else
                    (do
                      let w__737 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                       __opcode 5 1)) == (0b00000#5 : (BitVec 5))))))) : Bool) : Bool)
                        then
                          (do
                            let w__736 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__736 <b 2562) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__737 : Bool)
                      then
                        (do
                          writeReg SEE 2562
                          let sz := (BitVec.slice __opcode 22 1)
                          let Zm := (BitVec.slice __opcode 17 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let U := (BitVec.slice __opcode 4 1)
                          let S := (BitVec.slice __opcode 3 1)
                          let o1 := (BitVec.slice __opcode 0 1)
                          (decode_SMLALL_ZA_ZZW_2x2 sz Zm Rv Zn U S o1)
                          (pure false))
                      else
                        (do
                          let w__739 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 5 1)) == (0b00100#5 : (BitVec 5))))))) : Bool) : Bool)
                            then
                              (do
                                let w__738 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__738 <b 2563) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__739 : Bool)
                          then
                            (do
                              writeReg SEE 2563
                              let sz := (BitVec.slice __opcode 22 1)
                              let Zm := (BitVec.slice __opcode 17 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let Zn := (BitVec.slice __opcode 6 4)
                              let U := (BitVec.slice __opcode 4 1)
                              let S := (BitVec.slice __opcode 3 1)
                              let o1 := (BitVec.slice __opcode 0 1)
                              (decode_SMLSLL_ZA_ZZW_2x2 sz Zm Rv Zn U S o1)
                              (pure false))
                          else
                            (do
                              let w__741 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                             __opcode 5 1)) == (0b00010#5 : (BitVec 5)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__740 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__740 <b 2564) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__741 : Bool)
                              then
                                (do
                                  writeReg SEE 2564
                                  let sz := (BitVec.slice __opcode 22 1)
                                  let Zm := (BitVec.slice __opcode 17 4)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let Zn := (BitVec.slice __opcode 6 4)
                                  let U := (BitVec.slice __opcode 4 1)
                                  let S := (BitVec.slice __opcode 3 1)
                                  let o1 := (BitVec.slice __opcode 0 1)
                                  (decode_USMLALL_ZA_ZZW_S2x2 sz Zm Rv Zn U S o1)
                                  (pure false))
                              else
                                (do
                                  let w__743 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 4 1)) == (0x8#4 : (BitVec 4))))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__742 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__742 <b 2565) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__743 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2565
                                      let sz := (BitVec.slice __opcode 22 1)
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let U := (BitVec.slice __opcode 4 1)
                                      let S := (BitVec.slice __opcode 3 1)
                                      let o1 := (BitVec.slice __opcode 0 1)
                                      (decode_UMLALL_ZA_ZZV_2x1 sz Zm Rv Zn U S o1)
                                      (pure false))
                                  else
                                    (do
                                      let w__745 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 4 1)) == (0xC#4 : (BitVec 4))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__744 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__744 <b 2566) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__745 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2566
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let U := (BitVec.slice __opcode 4 1)
                                          let S := (BitVec.slice __opcode 3 1)
                                          let o1 := (BitVec.slice __opcode 0 1)
                                          (decode_UMLSLL_ZA_ZZV_2x1 sz Zm Rv Zn U S o1)
                                          (pure false))
                                      else
                                        (do
                                          let w__747 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 4 1)) == (0x0#4 : (BitVec 4))))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__746 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__746 <b 2567) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__747 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2567
                                              let sz := (BitVec.slice __opcode 22 1)
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let U := (BitVec.slice __opcode 4 1)
                                              let S := (BitVec.slice __opcode 3 1)
                                              let o1 := (BitVec.slice __opcode 0 1)
                                              (decode_SMLALL_ZA_ZZV_2x1 sz Zm Rv Zn U S o1)
                                              (pure false))
                                          else
                                            (do
                                              let w__749 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 4 1)) == (0x4#4 : (BitVec 4))))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__748 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__748 <b 2568) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__749 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2568
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let U := (BitVec.slice __opcode 4 1)
                                                  let S := (BitVec.slice __opcode 3 1)
                                                  let o1 := (BitVec.slice __opcode 0 1)
                                                  (decode_SMLSLL_ZA_ZZV_2x1 sz Zm Rv Zn U S o1)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__751 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 4 1)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__750 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__750 <b 2569) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__751 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2569
                                                      let sz := (BitVec.slice __opcode 22 1)
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let U := (BitVec.slice __opcode 4 1)
                                                      let S := (BitVec.slice __opcode 3 1)
                                                      let o1 := (BitVec.slice __opcode 0 1)
                                                      (decode_USMLALL_ZA_ZZV_S2x1 sz Zm Rv Zn U S o1)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__753 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 4 1)) == (0xA#4 : (BitVec 4)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__752 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__752 <b 2570) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__753 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2570
                                                          let sz := (BitVec.slice __opcode 22 1)
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let U := (BitVec.slice __opcode 4 1)
                                                          let S := (BitVec.slice __opcode 3 1)
                                                          let o1 := (BitVec.slice __opcode 0 1)
                                                          (decode_SUMLALL_ZA_ZZV_S2x1 sz Zm Rv Zn U
                                                            S o1)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__755 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 6 1)) == (0b001000#6 : (BitVec 6))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__754 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__754 <b 2571) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__755 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2571
                                                              let sz := (BitVec.slice __opcode 22 1)
                                                              let Zm := (BitVec.slice __opcode 18 3)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let U := (BitVec.slice __opcode 4 1)
                                                              let S := (BitVec.slice __opcode 3 1)
                                                              let o1 := (BitVec.slice __opcode 0 1)
                                                              (decode_UMLALL_ZA_ZZW_4x4 sz Zm Rv Zn
                                                                U S o1)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__757 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 6 1)) == (0b001100#6 : (BitVec 6))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__756 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__756 <b 2572) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__757 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2572
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 18 3)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 7 3)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let o1 :=
                                                                    (BitVec.slice __opcode 0 1)
                                                                  (decode_UMLSLL_ZA_ZZW_4x4 sz Zm Rv
                                                                    Zn U S o1)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__759 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 6 1)) == (0b000000#6 : (BitVec 6))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__758 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__758 <b 2573) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__759 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2573
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 18 3)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 7 3)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let o1 :=
                                                                        (BitVec.slice __opcode 0 1)
                                                                      (decode_SMLALL_ZA_ZZW_4x4 sz
                                                                        Zm Rv Zn U S o1)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__761 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 12
                                                                                       10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 6 1)) == (0b000100#6 : (BitVec 6))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__760 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__760 <b 2574) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__761 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2574
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              18 3)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 7
                                                                              3)
                                                                          let U :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let o1 :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_SMLSLL_ZA_ZZW_4x4
                                                                            sz Zm Rv Zn U S o1)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__763 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 17
                                                                                       15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 12
                                                                                         10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 6
                                                                                         1)) == (0b000010#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__762 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__762 <b 2575) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__763 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2575
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 3)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 3)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let o1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 1)
                                                                              (decode_USMLALL_ZA_ZZW_S4x4
                                                                                sz Zm Rv Zn U S o1)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__765 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 1)) == (0x8#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__764 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__764 <b 2576) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__765 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2576
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let o1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_UMLALL_ZA_ZZV_4x1
                                                                                    sz Zm Rv Zn U S
                                                                                    o1)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__767 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   12
                                                                                                   10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   1)) == (0xC#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__766 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__766 <b 2577) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__767 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2577
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let o1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          1)
                                                                                      (decode_UMLSLL_ZA_ZZV_4x1
                                                                                        sz Zm Rv Zn
                                                                                        U S o1)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__769 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       1)) == (0x0#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__768 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__768 <b 2578) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__769 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2578
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let o1 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 1)
                                                                                          (decode_SMLALL_ZA_ZZV_4x1
                                                                                            sz Zm Rv
                                                                                            Zn U S
                                                                                            o1)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__771 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           1)) == (0x4#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__770 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__770 <b 2579) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__771 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2579
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rv :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  1)
                                                                                              let o1 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  1)
                                                                                              (decode_SMLSLL_ZA_ZZV_4x1
                                                                                                sz
                                                                                                Zm
                                                                                                Rv
                                                                                                Zn U
                                                                                                S o1)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__773 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             12
                                                                                                             10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             1)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__772 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__772 <b 2580) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__773 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2580
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      1)
                                                                                                  let o1 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      1)
                                                                                                  (decode_USMLALL_ZA_ZZV_S4x1
                                                                                                    sz
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    Zn
                                                                                                    U
                                                                                                    S
                                                                                                    o1)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__775 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 1)) == (0xA#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__774 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__774 <b 2581) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__775 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2581
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          1)
                                                                                                      let o1 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          1)
                                                                                                      (decode_SUMLALL_ZA_ZZV_S4x1
                                                                                                        sz
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        Zn
                                                                                                        U
                                                                                                        S
                                                                                                        o1)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__777 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__776 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__776 <b 2582) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__777 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2582
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let i4h :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              15
                                                                                                              1)
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let i4l :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let off2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              2)
                                                                                                          (decode_UMLALL_ZA_ZZi_S
                                                                                                            Zm
                                                                                                            i4h
                                                                                                            Rv
                                                                                                            i4l
                                                                                                            Zn
                                                                                                            U
                                                                                                            S
                                                                                                            off2)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__779 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     2)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__778 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__778 <b 2583) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__779 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2583
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let i4h :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  15
                                                                                                                  1)
                                                                                                              let Rv :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let i4l :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  3)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  1)
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let off2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  2)
                                                                                                              (decode_UMLSLL_ZA_ZZi_S
                                                                                                                Zm
                                                                                                                i4h
                                                                                                                Rv
                                                                                                                i4l
                                                                                                                Zn
                                                                                                                U
                                                                                                                S
                                                                                                                off2)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__781 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__780 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__780 <b 2584) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__781 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2584
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let i4h :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      15
                                                                                                                      1)
                                                                                                                  let Rv :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let i4l :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      1)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let off2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      2)
                                                                                                                  (decode_SMLALL_ZA_ZZi_S
                                                                                                                    Zm
                                                                                                                    i4h
                                                                                                                    Rv
                                                                                                                    i4l
                                                                                                                    Zn
                                                                                                                    U
                                                                                                                    S
                                                                                                                    off2)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__783 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             2)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__782 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__782 <b 2585) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__783 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2585
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let i4h :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          15
                                                                                                                          1)
                                                                                                                      let Rv :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          2)
                                                                                                                      let i4l :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          1)
                                                                                                                      let off2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          2)
                                                                                                                      (decode_SMLSLL_ZA_ZZi_S
                                                                                                                        Zm
                                                                                                                        i4h
                                                                                                                        Rv
                                                                                                                        i4l
                                                                                                                        Zn
                                                                                                                        U
                                                                                                                        S
                                                                                                                        off2)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__785 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 2)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__784 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__784 <b 2586) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__785 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2586
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let i4h :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              15
                                                                                                                              1)
                                                                                                                          let Rv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let i4l :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              3
                                                                                                                              1)
                                                                                                                          let off2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              2)
                                                                                                                          (decode_USMLALL_ZA_ZZi_S
                                                                                                                            Zm
                                                                                                                            i4h
                                                                                                                            Rv
                                                                                                                            i4l
                                                                                                                            Zn
                                                                                                                            U
                                                                                                                            S
                                                                                                                            off2)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (pure true))))))))))))))))))))))))))))))


end ArmFull.Functions
