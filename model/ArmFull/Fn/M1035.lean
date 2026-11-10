import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0958
import ArmFull.Fn.M0959
import ArmFull.Fn.M0960

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
def __DecodeA64_SVE__seg11 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__951 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__950 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__950 <b 1512) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__951 : Bool)
  then
    (do
      writeReg SEE 1512
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let U := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_UQSUB_Z_ZZ__ size Zm U Zn Zd)
      (pure false))
  else
    (do
      let w__953 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 15 10)) == (0b000110#6 : (BitVec 6))))) : Bool) : Bool)
        then
          (do
            let w__952 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__952 <b 1513) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__953 : Bool)
      then
        (do
          writeReg SEE 1513
          let size := (BitVec.slice __opcode 22 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let U := (BitVec.slice __opcode 10 1)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_SQSUB_Z_ZZ__ size Zm U Zn Zd)
          (pure false))
      else
        (do
          let w__955 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                     __opcode 21 14)) == (0x97#8 : (BitVec 8)))) : Bool) : Bool)
            then
              (do
                let w__954 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__954 <b 1514) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__955 : Bool)
          then
            (do
              writeReg SEE 1514
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 16 1)
              let sh := (BitVec.slice __opcode 13 1)
              let imm8 := (BitVec.slice __opcode 5 8)
              let Zdn := (BitVec.slice __opcode 0 5)
              (decode_UQADD_Z_ZI__ size U sh imm8 Zdn)
              (pure false))
          else
            (do
              let w__957 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                         __opcode 21 14)) == (0x93#8 : (BitVec 8)))) : Bool) : Bool)
                then
                  (do
                    let w__956 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__956 <b 1515) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__957 : Bool)
              then
                (do
                  writeReg SEE 1515
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 16 1)
                  let sh := (BitVec.slice __opcode 13 1)
                  let imm8 := (BitVec.slice __opcode 5 8)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_SQADD_Z_ZI__ size U sh imm8 Zdn)
                  (pure false))
              else
                (do
                  let w__959 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                             __opcode 21 14)) == (0x9F#8 : (BitVec 8)))) : Bool) : Bool)
                    then
                      (do
                        let w__958 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__958 <b 1516) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__959 : Bool)
                  then
                    (do
                      writeReg SEE 1516
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 16 1)
                      let sh := (BitVec.slice __opcode 13 1)
                      let imm8 := (BitVec.slice __opcode 5 8)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_UQSUB_Z_ZI__ size U sh imm8 Zdn)
                      (pure false))
                  else
                    (do
                      let w__961 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                 __opcode 21 14)) == (0x9B#8 : (BitVec 8)))) : Bool) : Bool)
                        then
                          (do
                            let w__960 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__960 <b 1517) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__961 : Bool)
                      then
                        (do
                          writeReg SEE 1517
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 16 1)
                          let sh := (BitVec.slice __opcode 13 1)
                          let imm8 := (BitVec.slice __opcode 5 8)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_SQSUB_Z_ZI__ size U sh imm8 Zdn)
                          (pure false))
                      else
                        (do
                          let w__963 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0x250#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 15 14)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                            then
                              (do
                                let w__962 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__962 <b 1518) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__963 : Bool)
                          then
                            (do
                              writeReg SEE 1518
                              let S := (BitVec.slice __opcode 22 1)
                              let Pm := (BitVec.slice __opcode 16 4)
                              let Pg := (BitVec.slice __opcode 10 4)
                              let Pn := (BitVec.slice __opcode 5 4)
                              let B := (BitVec.slice __opcode 4 1)
                              let Pd := (BitVec.slice __opcode 0 4)
                              (decode_BRKPA_P_P_PP__ S Pm Pg Pn B Pd)
                              (pure false))
                          else
                            (do
                              let w__965 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0x254#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 15 14)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__964 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__964 <b 1519) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__965 : Bool)
                              then
                                (do
                                  writeReg SEE 1519
                                  let S := (BitVec.slice __opcode 22 1)
                                  let Pm := (BitVec.slice __opcode 16 4)
                                  let Pg := (BitVec.slice __opcode 10 4)
                                  let Pn := (BitVec.slice __opcode 5 4)
                                  let B := (BitVec.slice __opcode 4 1)
                                  let Pd := (BitVec.slice __opcode 0 4)
                                  (decode_BRKPAS_P_P_PP__ S Pm Pg Pn B Pd)
                                  (pure false))
                              else
                                (do
                                  let w__967 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0x250#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 15 14)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__966 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__966 <b 1520) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__967 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1520
                                      let S := (BitVec.slice __opcode 22 1)
                                      let Pm := (BitVec.slice __opcode 16 4)
                                      let Pg := (BitVec.slice __opcode 10 4)
                                      let Pn := (BitVec.slice __opcode 5 4)
                                      let B := (BitVec.slice __opcode 4 1)
                                      let Pd := (BitVec.slice __opcode 0 4)
                                      (decode_BRKPB_P_P_PP__ S Pm Pg Pn B Pd)
                                      (pure false))
                                  else
                                    (do
                                      let w__969 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0x254#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 15 14)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__968 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__968 <b 1521) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__969 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1521
                                          let S := (BitVec.slice __opcode 22 1)
                                          let Pm := (BitVec.slice __opcode 16 4)
                                          let Pg := (BitVec.slice __opcode 10 4)
                                          let Pn := (BitVec.slice __opcode 5 4)
                                          let B := (BitVec.slice __opcode 4 1)
                                          let Pd := (BitVec.slice __opcode 0 4)
                                          (decode_BRKPBS_P_P_PP__ S Pm Pg Pn B Pd)
                                          (pure false))
                                      else
                                        (do
                                          let w__971 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                     __opcode 31 14)) == (0b001001010001100001#18 : (BitVec 18))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__970 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__970 <b 1522) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__971 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1522
                                              let S := (BitVec.slice __opcode 22 1)
                                              let Pg := (BitVec.slice __opcode 10 4)
                                              let Pn := (BitVec.slice __opcode 5 4)
                                              let Pdm := (BitVec.slice __opcode 0 4)
                                              (decode_BRKN_P_P_PP__ S Pg Pn Pdm)
                                              (pure false))
                                          else
                                            (do
                                              let w__973 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                         __opcode 31 14)) == (0b001001010101100001#18 : (BitVec 18))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__972 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__972 <b 1523) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__973 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1523
                                                  let S := (BitVec.slice __opcode 22 1)
                                                  let Pg := (BitVec.slice __opcode 10 4)
                                                  let Pn := (BitVec.slice __opcode 5 4)
                                                  let Pdm := (BitVec.slice __opcode 0 4)
                                                  (decode_BRKNS_P_P_PP__ S Pg Pn Pdm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__975 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 21 10)) == (0xD0E#12 : (BitVec 12)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__974 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__974 <b 1524) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__975 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1524
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Vm := (BitVec.slice __opcode 5 5)
                                                      let Zdn := (BitVec.slice __opcode 0 5)
                                                      (decode_INSR_Z_V__ size Vm Zdn)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__977 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 21 10)) == (0x90E#12 : (BitVec 12)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__976 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__976 <b 1525) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__977 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1525
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Rm := (BitVec.slice __opcode 5 5)
                                                          let Zdn := (BitVec.slice __opcode 0 5)
                                                          (decode_INSR_Z_R__ size Rm Zdn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__979 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__978 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__978 <b 1526) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__979 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1526
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zda := (BitVec.slice __opcode 0 5)
                                                              (decode_SDOT_Z_ZZZ__ size Zm U Zn Zda)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__981 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__980 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__980 <b 1527) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__981 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1527
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let i2 :=
                                                                    (BitVec.slice __opcode 19 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 3)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zda :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_SDOT_Z_ZZZi_S size i2 Zm U
                                                                    Zn Zda)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__983 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__982 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__982 <b 1528) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__983 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1528
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let i1 :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zda :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_SDOT_Z_ZZZi_D size i1
                                                                        Zm U Zn Zda)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__985 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__984 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__984 <b 1529) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__985 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1529
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zda :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_UDOT_Z_ZZZ__ size
                                                                            Zm U Zn Zda)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__987 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__986 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__986 <b 1530) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__987 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1530
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let i2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 19 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 3)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zda :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_UDOT_Z_ZZZi_S
                                                                                size i2 Zm U Zn Zda)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__989 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__988 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__988 <b 1531) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__989 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1531
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let i1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zda :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_UDOT_Z_ZZZi_D
                                                                                    size i1 Zm U Zn
                                                                                    Zda)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__991 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b01000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b011110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__990 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__990 <b 1532) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__991 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1532
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zda :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_USDOT_Z_ZZZ_S
                                                                                        size Zm Zn
                                                                                        Zda)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__993 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b000110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__992 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__992 <b 1533) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__993 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1533
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let i2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              19 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 3)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zda :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_USDOT_Z_ZZZi_S
                                                                                            size i2
                                                                                            Zm U Zn
                                                                                            Zda)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__995 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__994 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__994 <b 1534) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__995 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1534
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let i2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  19
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  3)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  1)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Zda :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_SUDOT_Z_ZZZi_S
                                                                                                size
                                                                                                i2
                                                                                                Zm U
                                                                                                Zn
                                                                                                Zda)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__997 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b01000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b110010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__996 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__996 <b 1535) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__997 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1535
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      1)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Zda :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_SDOT_Z32_ZZZ__
                                                                                                    Zm
                                                                                                    U
                                                                                                    Zn
                                                                                                    Zda)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__999 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b01000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b110010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__998 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__998 <b 1536) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__999 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1536
                                                                                                      let i2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          19
                                                                                                          2)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          3)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          1)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zda :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_SDOT_Z32_ZZZi__
                                                                                                        i2
                                                                                                        Zm
                                                                                                        U
                                                                                                        Zn
                                                                                                        Zda)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1001 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b110011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1000 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1000 <b 1537) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1001 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1537
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              1)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zda :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_UDOT_Z32_ZZZ__
                                                                                                            Zm
                                                                                                            U
                                                                                                            Zn
                                                                                                            Zda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1003 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b110011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1002 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1002 <b 1538) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1003 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1538
                                                                                                              let i2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  19
                                                                                                                  2)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  3)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  1)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zda :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_UDOT_Z32_ZZZi__
                                                                                                                i2
                                                                                                                Zm
                                                                                                                U
                                                                                                                Zn
                                                                                                                Zda)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1005 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         13)) == (0b001000101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1004 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1004 <b 1539) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1005 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1539
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      19
                                                                                                                      1)
                                                                                                                  let Pg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
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
                                                                                                                  (decode_SQABS_Z_P_Z__
                                                                                                                    size
                                                                                                                    Q
                                                                                                                    Pg
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1007 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             13)) == (0b001001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1006 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1006 <b 1540) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1007 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1540
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          19
                                                                                                                          1)
                                                                                                                      let Pg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
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
                                                                                                                      (decode_SQNEG_Z_P_Z__
                                                                                                                        size
                                                                                                                        Q
                                                                                                                        Pg
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1009 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1008 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1008 <b 1541) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1009 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1541
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              1)
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
                                                                                                                          (decode_SQDMULH_Z_ZZ__
                                                                                                                            size
                                                                                                                            Zm
                                                                                                                            R
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1011 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1010 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1010 <b 1542) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1011 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1542
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let R :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
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
                                                                                                                              (decode_SQRDMULH_Z_ZZ__
                                                                                                                                size
                                                                                                                                Zm
                                                                                                                                R
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1013 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1012 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1012 <b 1543) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1013 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1543
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zda :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_SQRDMLAH_Z_ZZZ__
                                                                                                                                    size
                                                                                                                                    Zm
                                                                                                                                    S
                                                                                                                                    Zn
                                                                                                                                    Zda)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1015 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1014 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1014 <b 1544) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1015 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1544
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Zda :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_SQRDMLSH_Z_ZZZ__
                                                                                                                                        size
                                                                                                                                        Zm
                                                                                                                                        S
                                                                                                                                        Zn
                                                                                                                                        Zda)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1017 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 13)) == (0b010001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1016 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1016 <b 1545) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1017 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1545
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              1)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zdn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_ADDP_Z_P_ZZ__
                                                                                                                                            size
                                                                                                                                            U
                                                                                                                                            Pg
                                                                                                                                            Zm
                                                                                                                                            Zdn)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1019 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     13)) == (0b010101101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1018 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1018 <b 1546) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1019 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1546
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  1)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zdn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_UMAXP_Z_P_ZZ__
                                                                                                                                                size
                                                                                                                                                U
                                                                                                                                                Pg
                                                                                                                                                Zm
                                                                                                                                                Zdn)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1021 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         13)) == (0b010100101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1020 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1020 <b 1547) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1021 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1547
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      1)
                                                                                                                                                  let Pg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zdn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_SMAXP_Z_P_ZZ__
                                                                                                                                                    size
                                                                                                                                                    U
                                                                                                                                                    Pg
                                                                                                                                                    Zm
                                                                                                                                                    Zdn)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1023 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             21
                                                                                                                                                             13)) == (0b010111101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1022 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1022 <b 1548) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1023 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1548
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          1)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Zm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zdn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_UMINP_Z_P_ZZ__
                                                                                                                                                        size
                                                                                                                                                        U
                                                                                                                                                        Pg
                                                                                                                                                        Zm
                                                                                                                                                        Zdn)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1025 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 21
                                                                                                                                                                 13)) == (0b010110101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1024 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1024 <b 1549) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1025 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1549
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              1)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zdn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_SMINP_Z_P_ZZ__
                                                                                                                                                            size
                                                                                                                                                            U
                                                                                                                                                            Pg
                                                                                                                                                            Zm
                                                                                                                                                            Zdn)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__1027 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     21
                                                                                                                                                                     13)) == (0b000100101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__1026 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__1026 <b 1550) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__1027 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1550
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let U :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  1)
                                                                                                                                                              let Pg :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  3)
                                                                                                                                                              let Zn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Zda :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_SADALP_Z_P_Z__
                                                                                                                                                                size
                                                                                                                                                                U
                                                                                                                                                                Pg
                                                                                                                                                                Zn
                                                                                                                                                                Zda)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__1029 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         21
                                                                                                                                                                         13)) == (0b000101101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__1028 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__1028 <b 1551) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__1029 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1551
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      1)
                                                                                                                                                                  let Pg :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      3)
                                                                                                                                                                  let Zn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Zda :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_UADALP_Z_P_Z__
                                                                                                                                                                    size
                                                                                                                                                                    U
                                                                                                                                                                    Pg
                                                                                                                                                                    Zn
                                                                                                                                                                    Zda)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__1031 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               21
                                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               15
                                                                                                                                                                               10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__1030 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__1030 <b 1552) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__1031 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1552
                                                                                                                                                                      let tszh :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          1)
                                                                                                                                                                      let tszl :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          19
                                                                                                                                                                          2)
                                                                                                                                                                      let imm3 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          3)
                                                                                                                                                                      let U :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          1)
                                                                                                                                                                      let R :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          11
                                                                                                                                                                          1)
                                                                                                                                                                      let T :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          1)
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
                                                                                                                                                                      (decode_SHRNB_Z_ZI__
                                                                                                                                                                        tszh
                                                                                                                                                                        tszl
                                                                                                                                                                        imm3
                                                                                                                                                                        U
                                                                                                                                                                        R
                                                                                                                                                                        T
                                                                                                                                                                        Zn
                                                                                                                                                                        Zd)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__1033 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   21
                                                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__1032 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__1032 <b 1553) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__1033 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1553
                                                                                                                                                                          let tszh :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              1)
                                                                                                                                                                          let tszl :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              19
                                                                                                                                                                              2)
                                                                                                                                                                          let imm3 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              3)
                                                                                                                                                                          let U :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              1)
                                                                                                                                                                          let R :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              11
                                                                                                                                                                              1)
                                                                                                                                                                          let T :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              1)
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
                                                                                                                                                                          (decode_SHRNT_Z_ZI__
                                                                                                                                                                            tszh
                                                                                                                                                                            tszl
                                                                                                                                                                            imm3
                                                                                                                                                                            U
                                                                                                                                                                            R
                                                                                                                                                                            T
                                                                                                                                                                            Zn
                                                                                                                                                                            Zd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
