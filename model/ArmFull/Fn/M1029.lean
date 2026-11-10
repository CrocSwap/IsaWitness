import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0995
import ArmFull.Fn.M0996
import ArmFull.Fn.M0997

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
def __DecodeA64_SME__seg11 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__787 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC10#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 4 2)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__786 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__786 <b 2587) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__787 : Bool)
  then
    (do
      writeReg SEE 2587
      let Zm := (BitVec.slice __opcode 16 4)
      let i4h := (BitVec.slice __opcode 15 1)
      let Rv := (BitVec.slice __opcode 13 2)
      let i4l := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let U := (BitVec.slice __opcode 4 1)
      let S := (BitVec.slice __opcode 3 1)
      let off2 := (BitVec.slice __opcode 0 2)
      (decode_SUMLALL_ZA_ZZi_S Zm i4h Rv i4l Zn U S off2)
      (pure false))
  else
    (do
      let w__789 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 4 2)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
        then
          (do
            let w__788 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__788 <b 2588) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__789 : Bool)
      then
        (do
          writeReg SEE 2588
          let Zm := (BitVec.slice __opcode 16 4)
          let i3h := (BitVec.slice __opcode 15 1)
          let Rv := (BitVec.slice __opcode 13 2)
          let i3l := (BitVec.slice __opcode 10 2)
          let Zn := (BitVec.slice __opcode 5 5)
          let U := (BitVec.slice __opcode 4 1)
          let S := (BitVec.slice __opcode 3 1)
          let off2 := (BitVec.slice __opcode 0 2)
          (decode_UMLALL_ZA_ZZi_D Zm i3h Rv i3l Zn U S off2)
          (pure false))
      else
        (do
          let w__791 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 4 2)) == (0b110#3 : (BitVec 3))))) : Bool) : Bool)
            then
              (do
                let w__790 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__790 <b 2589) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__791 : Bool)
          then
            (do
              writeReg SEE 2589
              let Zm := (BitVec.slice __opcode 16 4)
              let i3h := (BitVec.slice __opcode 15 1)
              let Rv := (BitVec.slice __opcode 13 2)
              let i3l := (BitVec.slice __opcode 10 2)
              let Zn := (BitVec.slice __opcode 5 5)
              let U := (BitVec.slice __opcode 4 1)
              let S := (BitVec.slice __opcode 3 1)
              let off2 := (BitVec.slice __opcode 0 2)
              (decode_UMLSLL_ZA_ZZi_D Zm i3h Rv i3l Zn U S off2)
              (pure false))
          else
            (do
              let w__793 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 4 2)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                then
                  (do
                    let w__792 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__792 <b 2590) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__793 : Bool)
              then
                (do
                  writeReg SEE 2590
                  let Zm := (BitVec.slice __opcode 16 4)
                  let i3h := (BitVec.slice __opcode 15 1)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let i3l := (BitVec.slice __opcode 10 2)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let U := (BitVec.slice __opcode 4 1)
                  let S := (BitVec.slice __opcode 3 1)
                  let off2 := (BitVec.slice __opcode 0 2)
                  (decode_SMLALL_ZA_ZZi_D Zm i3h Rv i3l Zn U S off2)
                  (pure false))
              else
                (do
                  let w__795 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 4 2)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                    then
                      (do
                        let w__794 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__794 <b 2591) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__795 : Bool)
                  then
                    (do
                      writeReg SEE 2591
                      let Zm := (BitVec.slice __opcode 16 4)
                      let i3h := (BitVec.slice __opcode 15 1)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let i3l := (BitVec.slice __opcode 10 2)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let U := (BitVec.slice __opcode 4 1)
                      let S := (BitVec.slice __opcode 3 1)
                      let off2 := (BitVec.slice __opcode 0 2)
                      (decode_SMLSLL_ZA_ZZi_D Zm i3h Rv i3l Zn U S off2)
                      (pure false))
                  else
                    (do
                      let w__797 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 5 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                        then
                          (do
                            let w__796 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__796 <b 2592) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__797 : Bool)
                      then
                        (do
                          writeReg SEE 2592
                          let Zm := (BitVec.slice __opcode 16 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let i4h := (BitVec.slice __opcode 10 2)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let U := (BitVec.slice __opcode 4 1)
                          let S := (BitVec.slice __opcode 3 1)
                          let i4l := (BitVec.slice __opcode 1 2)
                          let o1 := (BitVec.slice __opcode 0 1)
                          (decode_UMLALL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                          (pure false))
                      else
                        (do
                          let w__799 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                            then
                              (do
                                let w__798 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__798 <b 2593) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__799 : Bool)
                          then
                            (do
                              writeReg SEE 2593
                              let Zm := (BitVec.slice __opcode 16 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let i4h := (BitVec.slice __opcode 10 2)
                              let Zn := (BitVec.slice __opcode 6 4)
                              let U := (BitVec.slice __opcode 4 1)
                              let S := (BitVec.slice __opcode 3 1)
                              let i4l := (BitVec.slice __opcode 1 2)
                              let o1 := (BitVec.slice __opcode 0 1)
                              (decode_UMLSLL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                              (pure false))
                          else
                            (do
                              let w__801 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 5 3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__800 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__800 <b 2594) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__801 : Bool)
                              then
                                (do
                                  writeReg SEE 2594
                                  let Zm := (BitVec.slice __opcode 16 4)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let i4h := (BitVec.slice __opcode 10 2)
                                  let Zn := (BitVec.slice __opcode 6 4)
                                  let U := (BitVec.slice __opcode 4 1)
                                  let S := (BitVec.slice __opcode 3 1)
                                  let i4l := (BitVec.slice __opcode 1 2)
                                  let o1 := (BitVec.slice __opcode 0 1)
                                  (decode_SMLALL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                                  (pure false))
                              else
                                (do
                                  let w__803 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__802 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__802 <b 2595) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__803 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2595
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let i4h := (BitVec.slice __opcode 10 2)
                                      let Zn := (BitVec.slice __opcode 6 4)
                                      let U := (BitVec.slice __opcode 4 1)
                                      let S := (BitVec.slice __opcode 3 1)
                                      let i4l := (BitVec.slice __opcode 1 2)
                                      let o1 := (BitVec.slice __opcode 0 1)
                                      (decode_SMLSLL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                                      (pure false))
                                  else
                                    (do
                                      let w__805 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 5 3)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__804 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__804 <b 2596) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__805 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2596
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let i4h := (BitVec.slice __opcode 10 2)
                                          let Zn := (BitVec.slice __opcode 6 4)
                                          let U := (BitVec.slice __opcode 4 1)
                                          let S := (BitVec.slice __opcode 3 1)
                                          let i4l := (BitVec.slice __opcode 1 2)
                                          let o1 := (BitVec.slice __opcode 0 1)
                                          (decode_USMLALL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                                          (pure false))
                                      else
                                        (do
                                          let w__807 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 5 3)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__806 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__806 <b 2597) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__807 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2597
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let i4h := (BitVec.slice __opcode 10 2)
                                              let Zn := (BitVec.slice __opcode 6 4)
                                              let U := (BitVec.slice __opcode 4 1)
                                              let S := (BitVec.slice __opcode 3 1)
                                              let i4l := (BitVec.slice __opcode 1 2)
                                              let o1 := (BitVec.slice __opcode 0 1)
                                              (decode_SUMLALL_ZA_ZZi_S2xi Zm Rv i4h Zn U S i4l o1)
                                              (pure false))
                                          else
                                            (do
                                              let w__809 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 5 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__808 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__808 <b 2598) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__809 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2598
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let i3h := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 6 4)
                                                  let U := (BitVec.slice __opcode 4 1)
                                                  let S := (BitVec.slice __opcode 3 1)
                                                  let i3l := (BitVec.slice __opcode 1 2)
                                                  let o1 := (BitVec.slice __opcode 0 1)
                                                  (decode_UMLALL_ZA_ZZi_D2xi Zm Rv i3h Zn U S i3l o1)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__811 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                 __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__810 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__810 <b 2599) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__811 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2599
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let i3h := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 6 4)
                                                      let U := (BitVec.slice __opcode 4 1)
                                                      let S := (BitVec.slice __opcode 3 1)
                                                      let i3l := (BitVec.slice __opcode 1 2)
                                                      let o1 := (BitVec.slice __opcode 0 1)
                                                      (decode_UMLSLL_ZA_ZZi_D2xi Zm Rv i3h Zn U S
                                                        i3l o1)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__813 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 5 3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__812 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__812 <b 2600) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__813 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2600
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let i3h := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 6 4)
                                                          let U := (BitVec.slice __opcode 4 1)
                                                          let S := (BitVec.slice __opcode 3 1)
                                                          let i3l := (BitVec.slice __opcode 1 2)
                                                          let o1 := (BitVec.slice __opcode 0 1)
                                                          (decode_SMLALL_ZA_ZZi_D2xi Zm Rv i3h Zn U
                                                            S i3l o1)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__815 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__814 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__814 <b 2601) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__815 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2601
                                                              let Zm := (BitVec.slice __opcode 16 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let i3h :=
                                                                (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 6 4)
                                                              let U := (BitVec.slice __opcode 4 1)
                                                              let S := (BitVec.slice __opcode 3 1)
                                                              let i3l := (BitVec.slice __opcode 1 2)
                                                              let o1 := (BitVec.slice __opcode 0 1)
                                                              (decode_SMLSLL_ZA_ZZi_D2xi Zm Rv i3h
                                                                Zn U S i3l o1)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__817 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 6 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__816 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__816 <b 2602) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__817 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2602
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let i4h :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 7 3)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let i4l :=
                                                                    (BitVec.slice __opcode 1 2)
                                                                  let o1 :=
                                                                    (BitVec.slice __opcode 0 1)
                                                                  (decode_UMLALL_ZA_ZZi_S4xi Zm Rv
                                                                    i4h Zn U S i4l o1)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__819 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__818 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__818 <b 2603) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__819 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2603
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let i4h :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 7 3)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let i4l :=
                                                                        (BitVec.slice __opcode 1 2)
                                                                      let o1 :=
                                                                        (BitVec.slice __opcode 0 1)
                                                                      (decode_UMLSLL_ZA_ZZi_S4xi Zm
                                                                        Rv i4h Zn U S i4l o1)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__821 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 6 3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__820 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__820 <b 2604) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__821 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2604
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let i4h :=
                                                                            (BitVec.slice __opcode
                                                                              10 2)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 7
                                                                              3)
                                                                          let U :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let i4l :=
                                                                            (BitVec.slice __opcode 1
                                                                              2)
                                                                          let o1 :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_SMLALL_ZA_ZZi_S4xi
                                                                            Zm Rv i4h Zn U S i4l o1)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__823 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 12
                                                                                         12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 6
                                                                                         3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__822 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__822 <b 2605) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__823 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2605
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let i4h :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 3)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let i4l :=
                                                                                (BitVec.slice
                                                                                  __opcode 1 2)
                                                                              let o1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 1)
                                                                              (decode_SMLSLL_ZA_ZZi_S4xi
                                                                                Zm Rv i4h Zn U S i4l
                                                                                o1)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__825 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             6 3)) == (0x4#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__824 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__824 <b 2606) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__825 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2606
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let i4h :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 3)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let i4l :=
                                                                                    (BitVec.slice
                                                                                      __opcode 1 2)
                                                                                  let o1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_USMLALL_ZA_ZZi_S4xi
                                                                                    Zm Rv i4h Zn U S
                                                                                    i4l o1)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__827 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 12
                                                                                                 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 6 3)) == (0x6#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__826 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__826 <b 2607) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__827 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2607
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let i4h :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          3)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let i4l :=
                                                                                        (BitVec.slice
                                                                                          __opcode 1
                                                                                          2)
                                                                                      let o1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          1)
                                                                                      (decode_SUMLALL_ZA_ZZi_S4xi
                                                                                        Zm Rv i4h Zn
                                                                                        U S i4l o1)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__829 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     12
                                                                                                     11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     6
                                                                                                     3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__828 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__828 <b 2608) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__829 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2608
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let i3h :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 3)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let i3l :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              1 2)
                                                                                          let o1 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 1)
                                                                                          (decode_UMLALL_ZA_ZZi_D4xi
                                                                                            Zm Rv
                                                                                            i3h Zn U
                                                                                            S i3l o1)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__831 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         12
                                                                                                         11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         6
                                                                                                         3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__830 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__830 <b 2609) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__831 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2609
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
                                                                                              let i3h :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  1)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  7
                                                                                                  3)
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
                                                                                              let i3l :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  1
                                                                                                  2)
                                                                                              let o1 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  1)
                                                                                              (decode_UMLSLL_ZA_ZZi_D4xi
                                                                                                Zm
                                                                                                Rv
                                                                                                i3h
                                                                                                Zn U
                                                                                                S
                                                                                                i3l
                                                                                                o1)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__833 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             12
                                                                                                             11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             6
                                                                                                             3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__832 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__832 <b 2610) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__833 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2610
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
                                                                                                  let i3h :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      1)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      3)
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
                                                                                                  let i3l :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      1
                                                                                                      2)
                                                                                                  let o1 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      1)
                                                                                                  (decode_SMLALL_ZA_ZZi_D4xi
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    i3h
                                                                                                    Zn
                                                                                                    U
                                                                                                    S
                                                                                                    i3l
                                                                                                    o1)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__835 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 6
                                                                                                                 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__834 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__834 <b 2611) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__835 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2611
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
                                                                                                      let i3h :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          1)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          7
                                                                                                          3)
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
                                                                                                      let i3l :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          1
                                                                                                          2)
                                                                                                      let o1 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          1)
                                                                                                      (decode_SMLSLL_ZA_ZZi_D4xi
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        i3h
                                                                                                        Zn
                                                                                                        U
                                                                                                        S
                                                                                                        i3l
                                                                                                        o1)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__837 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     3)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__836 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__836 <b 2612) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__837 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2612
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
                                                                                                          let off3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_UMLAL_ZA_ZZV_1
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            Zn
                                                                                                            U
                                                                                                            S
                                                                                                            off3)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__839 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__838 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__838 <b 2613) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__839 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2613
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
                                                                                                              let off3 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_UMLSL_ZA_ZZV_1
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                Zn
                                                                                                                U
                                                                                                                S
                                                                                                                off3)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__841 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             12
                                                                                                                             10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__840 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__840 <b 2614) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__841 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2614
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
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_SMLAL_ZA_ZZV_1
                                                                                                                    Zm
                                                                                                                    Rv
                                                                                                                    Zn
                                                                                                                    U
                                                                                                                    S
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__843 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 12
                                                                                                                                 10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__842 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__842 <b 2615) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__843 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2615
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
                                                                                                                      let off3 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_SMLSL_ZA_ZZV_1
                                                                                                                        Zm
                                                                                                                        Rv
                                                                                                                        Zn
                                                                                                                        U
                                                                                                                        S
                                                                                                                        off3)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__845 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   16
                                                                                                                                   15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     12
                                                                                                                                     10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     5
                                                                                                                                     2)) == (0x4#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__844 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__844 <b 2616) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__845 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2616
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              17
                                                                                                                              4)
                                                                                                                          let Rv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              4)
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
                                                                                                                          (decode_UMLAL_ZA_ZZW_2x2
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            Zn
                                                                                                                            U
                                                                                                                            S
                                                                                                                            off2)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (pure true))))))))))))))))))))))))))))))


end ArmFull.Functions
