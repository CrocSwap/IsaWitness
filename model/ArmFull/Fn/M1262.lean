import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0850
import ArmFull.Fn.M0919
import ArmFull.Fn.M0920
import ArmFull.Fn.M0921
import ArmFull.Fn.M0922
import ArmFull.Fn.M0998
import ArmFull.Fn.M0999
import ArmFull.Fn.M1168

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
def __DecodeA64_SME__seg14 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__993 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b110110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 6 5)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
    then
      (do
        let w__992 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__992 <b 2690) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__993 : Bool)
  then
    (do
      writeReg SEE 2690
      let tsize := (BitVec.slice __opcode 22 2)
      let imm5 := (BitVec.slice __opcode 16 5)
      let N := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 7 3)
      let U := (BitVec.slice __opcode 5 1)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_SQRSHRU_Z_MZ4__ tsize imm5 N Zn U Zd)
      (pure false))
  else
    (do
      let w__995 ← (( do
        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000100100011111000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 5 5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
        then
          (do
            let w__994 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__994 <b 2691) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__995 : Bool)
      then
        (do
          writeReg SEE 2691
          let Zn := (BitVec.slice __opcode 6 4)
          let U := (BitVec.slice __opcode 5 1)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_SQCVT_Z_MZ2__ Zn U Zd)
          (pure false))
      else
        (do
          let w__997 ← (( do
            if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000100100011111000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 5 5)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
            then
              (do
                let w__996 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__996 <b 2692) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__997 : Bool)
          then
            (do
              writeReg SEE 2692
              let Zn := (BitVec.slice __opcode 6 4)
              let U := (BitVec.slice __opcode 5 1)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_UQCVT_Z_MZ2__ Zn U Zd)
              (pure false))
          else
            (do
              let w__999 ← (( do
                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000101100011111000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 5 5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                then
                  (do
                    let w__998 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__998 <b 2693) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__999 : Bool)
              then
                (do
                  writeReg SEE 2693
                  let Zn := (BitVec.slice __opcode 6 4)
                  let U := (BitVec.slice __opcode 5 1)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_SQCVTU_Z_MZ2__ Zn U Zd)
                  (pure false))
              else
                (do
                  let w__1001 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                               __opcode 22 10)) == (0b0110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 6 5)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                    then
                      (do
                        let w__1000 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1000 <b 2694) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1001 : Bool)
                  then
                    (do
                      writeReg SEE 2694
                      let sz := (BitVec.slice __opcode 23 1)
                      let Zn := (BitVec.slice __opcode 7 3)
                      let N := (BitVec.slice __opcode 6 1)
                      let U := (BitVec.slice __opcode 5 1)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_SQCVTN_Z_MZ4__ sz Zn N U Zd)
                      (pure false))
                  else
                    (do
                      let w__1003 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                   __opcode 22 10)) == (0b0110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 6 5)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                        then
                          (do
                            let w__1002 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1002 <b 2695) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1003 : Bool)
                      then
                        (do
                          writeReg SEE 2695
                          let sz := (BitVec.slice __opcode 23 1)
                          let Zn := (BitVec.slice __opcode 7 3)
                          let N := (BitVec.slice __opcode 6 1)
                          let U := (BitVec.slice __opcode 5 1)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_UQCVTN_Z_MZ4__ sz Zn N U Zd)
                          (pure false))
                      else
                        (do
                          let w__1005 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                       __opcode 22 10)) == (0b1110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 6 5)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                            then
                              (do
                                let w__1004 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1004 <b 2696) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1005 : Bool)
                          then
                            (do
                              writeReg SEE 2696
                              let sz := (BitVec.slice __opcode 23 1)
                              let Zn := (BitVec.slice __opcode 7 3)
                              let N := (BitVec.slice __opcode 6 1)
                              let U := (BitVec.slice __opcode 5 1)
                              let Zd := (BitVec.slice __opcode 0 5)
                              (decode_SQCVTUN_Z_MZ4__ sz Zn N U Zd)
                              (pure false))
                          else
                            (do
                              let w__1007 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                           __opcode 22 10)) == (0b0110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 6 5)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1006 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1006 <b 2697) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1007 : Bool)
                              then
                                (do
                                  writeReg SEE 2697
                                  let sz := (BitVec.slice __opcode 23 1)
                                  let Zn := (BitVec.slice __opcode 7 3)
                                  let N := (BitVec.slice __opcode 6 1)
                                  let U := (BitVec.slice __opcode 5 1)
                                  let Zd := (BitVec.slice __opcode 0 5)
                                  (decode_SQCVT_Z_MZ4__ sz Zn N U Zd)
                                  (pure false))
                              else
                                (do
                                  let w__1009 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                               __opcode 22 10)) == (0b0110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 6 5)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1008 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1008 <b 2698) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1009 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2698
                                      let sz := (BitVec.slice __opcode 23 1)
                                      let Zn := (BitVec.slice __opcode 7 3)
                                      let N := (BitVec.slice __opcode 6 1)
                                      let U := (BitVec.slice __opcode 5 1)
                                      let Zd := (BitVec.slice __opcode 0 5)
                                      (decode_UQCVT_Z_MZ4__ sz Zn N U Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1011 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                   __opcode 22 10)) == (0b1110011111000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 6 5)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1010 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1010 <b 2699) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1011 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2699
                                          let sz := (BitVec.slice __opcode 23 1)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let N := (BitVec.slice __opcode 6 1)
                                          let U := (BitVec.slice __opcode 5 1)
                                          let Zd := (BitVec.slice __opcode 0 5)
                                          (decode_SQCVTU_Z_MZ4__ sz Zn N U Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1013 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                         __opcode 15 10)) == (0b110100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1012 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1012 <b 2700) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1013 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2700
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zd := (BitVec.slice __opcode 1 4)
                                              (decode_ZIP_MZ_ZZ_2 size Zm Zn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1015 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b110100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 0 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1014 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1014 <b 2701) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1015 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2701
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zd := (BitVec.slice __opcode 1 4)
                                                  (decode_UZP_MZ_ZZ_2 size Zm Zn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1017 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b110101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1016 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1016 <b 2702) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1017 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2702
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 1 4)
                                                      (decode_ZIP_MZ_ZZ_2Q Zm Zn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1019 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b110101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1018 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1018 <b 2703) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1019 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2703
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zd := (BitVec.slice __opcode 1 4)
                                                          (decode_UZP_MZ_ZZ_2Q Zm Zn Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1021 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                       __opcode 21 10)) == (0xDB8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1020 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1020 <b 2704) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1021 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2704
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let Zd := (BitVec.slice __opcode 2 3)
                                                              (decode_ZIP_MZ_Z_4 size Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1023 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                           __opcode 21 10)) == (0xDB8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 1 0)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1022 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1022 <b 2705) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1023 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2705
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 7 3)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 2 3)
                                                                  (decode_UZP_MZ_Z_4 size Zn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1025 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                             __opcode 31 10)) == (0b1100000100110111111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1024 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1024 <b 2706) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1025 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2706
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 7 3)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 2 3)
                                                                      (decode_ZIP_MZ_Z_4Q Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1027 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 10)) == (0b1100000100110111111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 1 0)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1026 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1026 <b 2707) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1027 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2707
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 7
                                                                              3)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 2
                                                                              3)
                                                                          (decode_UZP_MZ_Z_4Q Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1029 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 16
                                                                                         13)) == (0x4#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           0 0)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1028 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1028 <b 2708) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1029 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2708
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 4)
                                                                              let PNg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 4)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 1 4)
                                                                              (decode_SEL_MZ_P_ZZ_2
                                                                                size Zm PNg Zn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1031 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             17 13)) == (0b01100#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               1 0)) == (0b00#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1030 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1030 <b 2709) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1031 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2709
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 18 3)
                                                                                  let PNg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 3)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 2 3)
                                                                                  (decode_SEL_MZ_P_ZZ_4
                                                                                    size Zm PNg Zn
                                                                                    Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1033 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b10000000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 2)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1032 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1032 <b 2710) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1033 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2710
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Pm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 3)
                                                                                      let Pn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let ZAda :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          2)
                                                                                      (decode_BMOPA_ZA_PP_ZZ_32
                                                                                        Zm Pm Pn Zn
                                                                                        S ZAda)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1035 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b10000000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 2)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1034 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1034 <b 2711) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1035 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2711
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let Pm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 3)
                                                                                          let Pn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let ZAda :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 2)
                                                                                          (decode_BMOPS_ZA_PP_ZZ_32
                                                                                            Zm Pm Pn
                                                                                            Zn S
                                                                                            ZAda)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1037 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b10100000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     2)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1036 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1036 <b 2712) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1037 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2712
                                                                                              let u0 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  24
                                                                                                  1)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let Pm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  3)
                                                                                              let Pn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let ZAda :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  2)
                                                                                              (decode_SMOPA_ZA32_PP_ZZ_16
                                                                                                u0
                                                                                                Zm
                                                                                                Pm
                                                                                                Pn
                                                                                                Zn S
                                                                                                ZAda)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1039 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b10100001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         2)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1038 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1038 <b 2713) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1039 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2713
                                                                                                  let u0 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      24
                                                                                                      1)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let Pm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      3)
                                                                                                  let Pn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let ZAda :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      2)
                                                                                                  (decode_UMOPA_ZA32_PP_ZZ_16
                                                                                                    u0
                                                                                                    Zm
                                                                                                    Pm
                                                                                                    Pn
                                                                                                    Zn
                                                                                                    S
                                                                                                    ZAda)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1041 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b10100000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             2)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1040 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1040 <b 2714) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1041 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2714
                                                                                                      let u0 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          24
                                                                                                          1)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let Pm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          3)
                                                                                                      let Pn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let ZAda :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          2)
                                                                                                      (decode_SMOPS_ZA32_PP_ZZ_16
                                                                                                        u0
                                                                                                        Zm
                                                                                                        Pm
                                                                                                        Pn
                                                                                                        Zn
                                                                                                        S
                                                                                                        ZAda)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1043 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b10100001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 2)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1042 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1042 <b 2715) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1043 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2715
                                                                                                          let u0 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              24
                                                                                                              1)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let Pm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              3)
                                                                                                          let Pn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let ZAda :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              2)
                                                                                                          (decode_UMOPS_ZA32_PP_ZZ_16
                                                                                                            u0
                                                                                                            Zm
                                                                                                            Pm
                                                                                                            Pn
                                                                                                            Zn
                                                                                                            S
                                                                                                            ZAda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1045 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     18)) == (0b11000000110011#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1044 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1044 <b 2716) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1045 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2716
                                                                                                              let i4 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  14
                                                                                                                  4)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  2)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_LUTI2_Z_ZTZ__
                                                                                                                i4
                                                                                                                size
                                                                                                                Zn
                                                                                                                Zd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1047 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         17)) == (0b110000001100101#15 : (BitVec 15))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1046 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1046 <b 2717) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1047 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2717
                                                                                                                  let i3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      14
                                                                                                                      3)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      2)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Zd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_LUTI4_Z_ZTZ__
                                                                                                                    i3
                                                                                                                    size
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1049 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             18)) == (0b11000000100011#14 : (BitVec 14))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               14
                                                                                                                               14)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 0
                                                                                                                                 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1048 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1048 <b 2718) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1049 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2718
                                                                                                                      let i3 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          15
                                                                                                                          3)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          2)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Zd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          1
                                                                                                                          4)
                                                                                                                      (decode_LUTI2_MZ2_ZTZ_1
                                                                                                                        i3
                                                                                                                        size
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1051 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 17)) == (0b110000001000101#15 : (BitVec 15))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   14
                                                                                                                                   14)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     0
                                                                                                                                     0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1050 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1050 <b 2719) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1051 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2719
                                                                                                                          let i2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              15
                                                                                                                              2)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Zd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              1
                                                                                                                              4)
                                                                                                                          (decode_LUTI4_MZ2_ZTZ_1
                                                                                                                            i2
                                                                                                                            size
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1053 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     18)) == (0b11000000100011#14 : (BitVec 14))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       14)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         11
                                                                                                                                         10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         1
                                                                                                                                         0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1052 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1052 <b 2720) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1053 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2720
                                                                                                                              let i2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  2)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let Zd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  2
                                                                                                                                  3)
                                                                                                                              (decode_LUTI2_MZ4_ZTZ_1
                                                                                                                                i2
                                                                                                                                size
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1055 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         17)) == (0b110000001000101#15 : (BitVec 15))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           14)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             1
                                                                                                                                             0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1054 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1054 <b 2721) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1055 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2721
                                                                                                                                  let i1 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      1)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      2
                                                                                                                                      3)
                                                                                                                                  (decode_LUTI4_MZ4_ZTZ_1
                                                                                                                                    i1
                                                                                                                                    size
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1057 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             10)) == (0b1110000100011111100000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1056 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1056 <b 2722) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1057 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2722
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      (decode_LDR_ZT_BR__
                                                                                                                                        Rn)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1059 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 10)) == (0b1110000100111111100000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1058 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1058 <b 2723) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1059 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2723
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          (decode_STR_ZT_BR__
                                                                                                                                            Rn)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1061 ← (( do
                                                                                                                                            if (((__opcode == 0b11000000010010000000000000000001#32) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1060 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1060 <b 2724) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1061 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2724
                                                                                                                                              (decode_ZERO_ZT_I__
                                                                                                                                                ())
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1063 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         15)) == (0b11000000010011000#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         5)) == (0b0011111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1062 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1062 <b 2725) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1063 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2725
                                                                                                                                                  let off3 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      3)
                                                                                                                                                  let Rt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_MOVT_R_ZT__
                                                                                                                                                    off3
                                                                                                                                                    Rt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1065 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             15)) == (0b11000000010011100#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             11
                                                                                                                                                             5)) == (0b0011111#7 : (BitVec 7)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1064 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1064 <b 2726) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1065 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2726
                                                                                                                                                      let off3 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          3)
                                                                                                                                                      let Rt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_MOVT_ZT_R__
                                                                                                                                                        off3
                                                                                                                                                        Rt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1067 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 15)) == (0b11000000000011000#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 12
                                                                                                                                                                 3)) == (0b0000000000#10 : (BitVec 10)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1066 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1066 <b 2730) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1067 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2730
                                                                                                                                                          let Rv :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              2)
                                                                                                                                                          let off3 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              3)
                                                                                                                                                          (decode_ZERO_ZA1_RI_2
                                                                                                                                                            Rv
                                                                                                                                                            off3)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__1069 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     15)) == (0b11000000000011100#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     12
                                                                                                                                                                     3)) == (0b0000000000#10 : (BitVec 10)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__1068 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__1068 <b 2731) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__1069 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2731
                                                                                                                                                              let Rv :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  13
                                                                                                                                                                  2)
                                                                                                                                                              let off3 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  3)
                                                                                                                                                              (decode_ZERO_ZA1_RI_4
                                                                                                                                                                Rv
                                                                                                                                                                off3)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__1071 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         15)) == (0b11000000000011001#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         12
                                                                                                                                                                         3)) == (0b0000000000#10 : (BitVec 10)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__1070 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__1070 <b 2732) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__1071 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2732
                                                                                                                                                                  let Rv :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      13
                                                                                                                                                                      2)
                                                                                                                                                                  let off3 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      3)
                                                                                                                                                                  (decode_ZERO_ZA2_RI_1
                                                                                                                                                                    Rv
                                                                                                                                                                    off3)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__1073 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             15)) == (0b11000000000011010#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             12
                                                                                                                                                                             2)) == (0b00000000000#11 : (BitVec 11)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__1072 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__1072 <b 2733) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__1073 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 2733
                                                                                                                                                                      let Rv :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          13
                                                                                                                                                                          2)
                                                                                                                                                                      let off2 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          2)
                                                                                                                                                                      (decode_ZERO_ZA2_RI_2
                                                                                                                                                                        Rv
                                                                                                                                                                        off2)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__1075 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 15)) == (0b11000000000011011#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 12
                                                                                                                                                                                 2)) == (0b00000000000#11 : (BitVec 11)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__1074 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__1074 <b 2734) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__1075 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 2734
                                                                                                                                                                          let Rv :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              13
                                                                                                                                                                              2)
                                                                                                                                                                          let off2 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              2)
                                                                                                                                                                          (decode_ZERO_ZA2_RI_4
                                                                                                                                                                            Rv
                                                                                                                                                                            off2)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__1077 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     15)) == (0b11000000000011101#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     12
                                                                                                                                                                                     2)) == (0b00000000000#11 : (BitVec 11)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__1076 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__1076 <b 2735) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__1077 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 2735
                                                                                                                                                                              let Rv :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  13
                                                                                                                                                                                  2)
                                                                                                                                                                              let off2 :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  2)
                                                                                                                                                                              (decode_ZERO_ZA4_RI_1
                                                                                                                                                                                Rv
                                                                                                                                                                                off2)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__1079 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         15)) == (0b11000000000011110#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         12
                                                                                                                                                                                         1)) == (0x000#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__1078 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__1078 <b 2736) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__1079 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 2736
                                                                                                                                                                                  let Rv :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      13
                                                                                                                                                                                      2)
                                                                                                                                                                                  let o1 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      1)
                                                                                                                                                                                  (decode_ZERO_ZA4_RI_2
                                                                                                                                                                                    Rv
                                                                                                                                                                                    o1)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__1081 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             15)) == (0b11000000000011111#17 : (BitVec 17))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             12
                                                                                                                                                                                             1)) == (0x000#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__1080 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__1080 <b 2737) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__1081 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 2737
                                                                                                                                                                                      let Rv :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          13
                                                                                                                                                                                          2)
                                                                                                                                                                                      let o1 :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          1)
                                                                                                                                                                                      (decode_ZERO_ZA4_RI_4
                                                                                                                                                                                        Rv
                                                                                                                                                                                        o1)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__1083 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 18)) == (0b11000000100111#14 : (BitVec 14))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   14
                                                                                                                                                                                                   14)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     11
                                                                                                                                                                                                     10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     3
                                                                                                                                                                                                     3)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__1082 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__1082 <b 2738) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__1083 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 2738
                                                                                                                                                                                          let i3 :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              15
                                                                                                                                                                                              3)
                                                                                                                                                                                          let size :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              12
                                                                                                                                                                                              2)
                                                                                                                                                                                          let Zn :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              5
                                                                                                                                                                                              5)
                                                                                                                                                                                          let D :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              4
                                                                                                                                                                                              1)
                                                                                                                                                                                          let Zd :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              0
                                                                                                                                                                                              3)
                                                                                                                                                                                          (decode_LUTI2_MZ2_ZTZ_8
                                                                                                                                                                                            i3
                                                                                                                                                                                            size
                                                                                                                                                                                            Zn
                                                                                                                                                                                            D
                                                                                                                                                                                            Zd)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__1085 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     31
                                                                                                                                                                                                     17)) == (0b110000001001101#15 : (BitVec 15))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       14
                                                                                                                                                                                                       14)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         11
                                                                                                                                                                                                         10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         3
                                                                                                                                                                                                         3)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__1084 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__1084 <b 2739) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__1085 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 2739
                                                                                                                                                                                              let i2 :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  15
                                                                                                                                                                                                  2)
                                                                                                                                                                                              let size :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  12
                                                                                                                                                                                                  2)
                                                                                                                                                                                              let Zn :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  5
                                                                                                                                                                                                  5)
                                                                                                                                                                                              let D :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  4
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let Zd :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  3)
                                                                                                                                                                                              (decode_LUTI4_MZ2_ZTZ_8
                                                                                                                                                                                                i2
                                                                                                                                                                                                size
                                                                                                                                                                                                Zn
                                                                                                                                                                                                D
                                                                                                                                                                                                Zd)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
