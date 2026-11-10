import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0961
import ArmFull.Fn.M0962
import ArmFull.Fn.M0963
import ArmFull.Fn.M0964

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
def __DecodeA64_SVE__seg12 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1035 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b000110#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__1034 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1034 <b 1554) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1035 : Bool)
  then
    (do
      writeReg SEE 1554
      let tszh := (BitVec.slice __opcode 22 1)
      let tszl := (BitVec.slice __opcode 19 2)
      let imm3 := (BitVec.slice __opcode 16 3)
      let U := (BitVec.slice __opcode 12 1)
      let R := (BitVec.slice __opcode 11 1)
      let T := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_RSHRNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
      (pure false))
  else
    (do
      let w__1037 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 15 10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
        then
          (do
            let w__1036 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1036 <b 1555) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1037 : Bool)
      then
        (do
          writeReg SEE 1555
          let tszh := (BitVec.slice __opcode 22 1)
          let tszl := (BitVec.slice __opcode 19 2)
          let imm3 := (BitVec.slice __opcode 16 3)
          let U := (BitVec.slice __opcode 12 1)
          let R := (BitVec.slice __opcode 11 1)
          let T := (BitVec.slice __opcode 10 1)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_RSHRNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
          (pure false))
      else
        (do
          let w__1039 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b001000#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__1038 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1038 <b 1556) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1039 : Bool)
          then
            (do
              writeReg SEE 1556
              let tszh := (BitVec.slice __opcode 22 1)
              let tszl := (BitVec.slice __opcode 19 2)
              let imm3 := (BitVec.slice __opcode 16 3)
              let U := (BitVec.slice __opcode 12 1)
              let R := (BitVec.slice __opcode 11 1)
              let T := (BitVec.slice __opcode 10 1)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_SQSHRNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
              (pure false))
          else
            (do
              let w__1041 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 15 10)) == (0b001001#6 : (BitVec 6))))) : Bool) : Bool)
                then
                  (do
                    let w__1040 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1040 <b 1557) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1041 : Bool)
              then
                (do
                  writeReg SEE 1557
                  let tszh := (BitVec.slice __opcode 22 1)
                  let tszl := (BitVec.slice __opcode 19 2)
                  let imm3 := (BitVec.slice __opcode 16 3)
                  let U := (BitVec.slice __opcode 12 1)
                  let R := (BitVec.slice __opcode 11 1)
                  let T := (BitVec.slice __opcode 10 1)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_SQSHRNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                  (pure false))
              else
                (do
                  let w__1043 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__1042 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1042 <b 1558) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1043 : Bool)
                  then
                    (do
                      writeReg SEE 1558
                      let tszh := (BitVec.slice __opcode 22 1)
                      let tszl := (BitVec.slice __opcode 19 2)
                      let imm3 := (BitVec.slice __opcode 16 3)
                      let U := (BitVec.slice __opcode 12 1)
                      let R := (BitVec.slice __opcode 11 1)
                      let T := (BitVec.slice __opcode 10 1)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_UQSHRNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__1045 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                        then
                          (do
                            let w__1044 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1044 <b 1559) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1045 : Bool)
                      then
                        (do
                          writeReg SEE 1559
                          let tszh := (BitVec.slice __opcode 22 1)
                          let tszl := (BitVec.slice __opcode 19 2)
                          let imm3 := (BitVec.slice __opcode 16 3)
                          let U := (BitVec.slice __opcode 12 1)
                          let R := (BitVec.slice __opcode 11 1)
                          let T := (BitVec.slice __opcode 10 1)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_UQSHRNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__1047 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 15 10)) == (0b001010#6 : (BitVec 6))))) : Bool) : Bool)
                            then
                              (do
                                let w__1046 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1046 <b 1560) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1047 : Bool)
                          then
                            (do
                              writeReg SEE 1560
                              let tszh := (BitVec.slice __opcode 22 1)
                              let tszl := (BitVec.slice __opcode 19 2)
                              let imm3 := (BitVec.slice __opcode 16 3)
                              let U := (BitVec.slice __opcode 12 1)
                              let R := (BitVec.slice __opcode 11 1)
                              let T := (BitVec.slice __opcode 10 1)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zd := (BitVec.slice __opcode 0 5)
                              (decode_SQRSHRNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                              (pure false))
                          else
                            (do
                              let w__1049 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 15 10)) == (0b001011#6 : (BitVec 6))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1048 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1048 <b 1561) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1049 : Bool)
                              then
                                (do
                                  writeReg SEE 1561
                                  let tszh := (BitVec.slice __opcode 22 1)
                                  let tszl := (BitVec.slice __opcode 19 2)
                                  let imm3 := (BitVec.slice __opcode 16 3)
                                  let U := (BitVec.slice __opcode 12 1)
                                  let R := (BitVec.slice __opcode 11 1)
                                  let T := (BitVec.slice __opcode 10 1)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zd := (BitVec.slice __opcode 0 5)
                                  (decode_SQRSHRNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                                  (pure false))
                              else
                                (do
                                  let w__1051 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b001110#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1050 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1050 <b 1562) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1051 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1562
                                      let tszh := (BitVec.slice __opcode 22 1)
                                      let tszl := (BitVec.slice __opcode 19 2)
                                      let imm3 := (BitVec.slice __opcode 16 3)
                                      let U := (BitVec.slice __opcode 12 1)
                                      let R := (BitVec.slice __opcode 11 1)
                                      let T := (BitVec.slice __opcode 10 1)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zd := (BitVec.slice __opcode 0 5)
                                      (decode_UQRSHRNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1053 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1052 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1052 <b 1563) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1053 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1563
                                          let tszh := (BitVec.slice __opcode 22 1)
                                          let tszl := (BitVec.slice __opcode 19 2)
                                          let imm3 := (BitVec.slice __opcode 16 3)
                                          let U := (BitVec.slice __opcode 12 1)
                                          let R := (BitVec.slice __opcode 11 1)
                                          let T := (BitVec.slice __opcode 10 1)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zd := (BitVec.slice __opcode 0 5)
                                          (decode_UQRSHRNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1055 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1054 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1054 <b 1564) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1055 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1564
                                              let tszh := (BitVec.slice __opcode 22 1)
                                              let tszl := (BitVec.slice __opcode 19 2)
                                              let imm3 := (BitVec.slice __opcode 16 3)
                                              let U := (BitVec.slice __opcode 12 1)
                                              let R := (BitVec.slice __opcode 11 1)
                                              let T := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zd := (BitVec.slice __opcode 0 5)
                                              (decode_SQSHRUNB_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1057 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1056 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1056 <b 1565) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1057 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1565
                                                  let tszh := (BitVec.slice __opcode 22 1)
                                                  let tszl := (BitVec.slice __opcode 19 2)
                                                  let imm3 := (BitVec.slice __opcode 16 3)
                                                  let U := (BitVec.slice __opcode 12 1)
                                                  let R := (BitVec.slice __opcode 11 1)
                                                  let T := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zd := (BitVec.slice __opcode 0 5)
                                                  (decode_SQSHRUNT_Z_ZI__ tszh tszl imm3 U R T Zn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1059 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1058 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1058 <b 1566) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1059 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1566
                                                      let tszh := (BitVec.slice __opcode 22 1)
                                                      let tszl := (BitVec.slice __opcode 19 2)
                                                      let imm3 := (BitVec.slice __opcode 16 3)
                                                      let U := (BitVec.slice __opcode 12 1)
                                                      let R := (BitVec.slice __opcode 11 1)
                                                      let T := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_SQRSHRUNB_Z_ZI__ tszh tszl imm3 U R T
                                                        Zn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1061 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1060 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1060 <b 1567) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1061 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1567
                                                          let tszh := (BitVec.slice __opcode 22 1)
                                                          let tszl := (BitVec.slice __opcode 19 2)
                                                          let imm3 := (BitVec.slice __opcode 16 3)
                                                          let U := (BitVec.slice __opcode 12 1)
                                                          let R := (BitVec.slice __opcode 11 1)
                                                          let T := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zd := (BitVec.slice __opcode 0 5)
                                                          (decode_SQRSHRUNT_Z_ZI__ tszh tszl imm3 U
                                                            R T Zn Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1063 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 21 13)) == (0b001100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1062 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1062 <b 1568) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1063 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1568
                                                              let tszh :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let L := (BitVec.slice __opcode 17 1)
                                                              let U := (BitVec.slice __opcode 16 1)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let tszl :=
                                                                (BitVec.slice __opcode 8 2)
                                                              let imm3 :=
                                                                (BitVec.slice __opcode 5 3)
                                                              let Zdn := (BitVec.slice __opcode 0 5)
                                                              (decode_SRSHR_Z_P_ZI__ tszh L U Pg
                                                                tszl imm3 Zdn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1065 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 21 13)) == (0b001101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1064 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1064 <b 1569) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1065 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1569
                                                                  let tszh :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let L :=
                                                                    (BitVec.slice __opcode 17 1)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 16 1)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let tszl :=
                                                                    (BitVec.slice __opcode 8 2)
                                                                  let imm3 :=
                                                                    (BitVec.slice __opcode 5 3)
                                                                  let Zdn :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_URSHR_Z_P_ZI__ tszh L U Pg
                                                                    tszl imm3 Zdn)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1067 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 21 13)) == (0b000110100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1066 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1066 <b 1570) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1067 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1570
                                                                      let tszh :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let L :=
                                                                        (BitVec.slice __opcode 17 1)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 16 1)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let tszl :=
                                                                        (BitVec.slice __opcode 8 2)
                                                                      let imm3 :=
                                                                        (BitVec.slice __opcode 5 3)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_SQSHL_Z_P_ZI__ tszh L
                                                                        U Pg tszl imm3 Zdn)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1069 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 21 13)) == (0b000111100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1068 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1068 <b 1571) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1069 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1571
                                                                          let tszh :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let L :=
                                                                            (BitVec.slice __opcode
                                                                              17 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              16 1)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let tszl :=
                                                                            (BitVec.slice __opcode 8
                                                                              2)
                                                                          let imm3 :=
                                                                            (BitVec.slice __opcode 5
                                                                              3)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_UQSHL_Z_P_ZI__
                                                                            tszh L U Pg tszl imm3
                                                                            Zdn)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1071 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 13)) == (0b001111100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1070 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1070 <b 1572) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1071 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1572
                                                                              let tszh :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let tszl :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 2)
                                                                              let imm3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 3)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_SQSHLU_Z_P_ZI__
                                                                                tszh L U Pg tszl
                                                                                imm3 Zdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1073 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1072 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1072 <b 1573) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1073 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1573
                                                                                  let tszh :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let tszl :=
                                                                                    (BitVec.slice
                                                                                      __opcode 19 2)
                                                                                  let imm3 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 3)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let T :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_SSHLLB_Z_ZI__
                                                                                    tszh tszl imm3 U
                                                                                    T Zn Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1075 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b101001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1074 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1074 <b 1574) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1075 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1574
                                                                                      let tszh :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let tszl :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          19 2)
                                                                                      let imm3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 3)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
                                                                                      let T :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 1)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_SSHLLT_Z_ZI__
                                                                                        tszh tszl
                                                                                        imm3 U T Zn
                                                                                        Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1077 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b101010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1076 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1076 <b 1575) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1077 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1575
                                                                                          let tszh :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let tszl :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              19 2)
                                                                                          let imm3 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 3)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
                                                                                          let T :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_USHLLB_Z_ZI__
                                                                                            tszh
                                                                                            tszl
                                                                                            imm3 U T
                                                                                            Zn Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1079 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b101011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1078 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1078 <b 1576) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1079 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1576
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
                                                                                              (decode_USHLLT_Z_ZI__
                                                                                                tszh
                                                                                                tszl
                                                                                                imm3
                                                                                                U T
                                                                                                Zn
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1081 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           18
                                                                                                           10)) == (0b000010000#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1080 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1080 <b 1577) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1081 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1577
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
                                                                                                  let U :=
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
                                                                                                  (decode_SQXTNB_Z_ZZ__
                                                                                                    tszh
                                                                                                    tszl
                                                                                                    U
                                                                                                    T
                                                                                                    Zn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1083 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               18
                                                                                                               10)) == (0b000010010#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1082 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1082 <b 1578) : Bool))))
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
                                                                                                      writeReg SEE 1578
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
                                                                                                      let U :=
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
                                                                                                      (decode_UQXTNB_Z_ZZ__
                                                                                                        tszh
                                                                                                        tszl
                                                                                                        U
                                                                                                        T
                                                                                                        Zn
                                                                                                        Zd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1085 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   18
                                                                                                                   10)) == (0b000010100#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1084 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1084 <b 1579) : Bool))))
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
                                                                                                          writeReg SEE 1579
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
                                                                                                          (decode_SQXTUNB_Z_ZZ__
                                                                                                            tszh
                                                                                                            tszl
                                                                                                            T
                                                                                                            Zn
                                                                                                            Zd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1087 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       18
                                                                                                                       10)) == (0b000010001#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1086 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1086 <b 1580) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1087 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1580
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
                                                                                                              let U :=
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
                                                                                                              (decode_SQXTNT_Z_ZZ__
                                                                                                                tszh
                                                                                                                tszl
                                                                                                                U
                                                                                                                T
                                                                                                                Zn
                                                                                                                Zd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1089 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           18
                                                                                                                           10)) == (0b000010011#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1088 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1088 <b 1581) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1089 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1581
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
                                                                                                                  let U :=
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
                                                                                                                  (decode_UQXTNT_Z_ZZ__
                                                                                                                    tszh
                                                                                                                    tszl
                                                                                                                    U
                                                                                                                    T
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1091 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               18
                                                                                                                               10)) == (0b000010101#9 : (BitVec 9))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1090 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1090 <b 1582) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1091 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1582
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
                                                                                                                      (decode_SQXTUNT_Z_ZZ__
                                                                                                                        tszh
                                                                                                                        tszl
                                                                                                                        T
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1093 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1092 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1092 <b 1583) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1093 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1583
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
                                                                                                                          let U :=
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
                                                                                                                          (decode_SMULLT_Z_ZZ__
                                                                                                                            size
                                                                                                                            Zm
                                                                                                                            U
                                                                                                                            T
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1095 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1094 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1094 <b 1584) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1095 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1584
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
                                                                                                                              let U :=
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
                                                                                                                              (decode_SMULLB_Z_ZZ__
                                                                                                                                size
                                                                                                                                Zm
                                                                                                                                U
                                                                                                                                T
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1097 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b011111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1096 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1096 <b 1585) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1097 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1585
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
                                                                                                                                  let U :=
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
                                                                                                                                  (decode_UMULLT_Z_ZZ__
                                                                                                                                    size
                                                                                                                                    Zm
                                                                                                                                    U
                                                                                                                                    T
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1099 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b011110#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1098 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1098 <b 1586) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1099 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1586
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
                                                                                                                                      let U :=
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
                                                                                                                                      (decode_UMULLB_Z_ZZ__
                                                                                                                                        size
                                                                                                                                        Zm
                                                                                                                                        U
                                                                                                                                        T
                                                                                                                                        Zn
                                                                                                                                        Zd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1101 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1100 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1100 <b 1587) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1101 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1587
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
                                                                                                                                          let U :=
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
                                                                                                                                          (decode_SQDMULLT_Z_ZZ__
                                                                                                                                            size
                                                                                                                                            Zm
                                                                                                                                            U
                                                                                                                                            T
                                                                                                                                            Zn
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
