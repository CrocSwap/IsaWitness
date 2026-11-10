import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1054
import ArmFull.Fn.M1055
import ArmFull.Fn.M1056
import ArmFull.Fn.M1057
import ArmFull.Fn.M1058
import ArmFull.Fn.M1093
import ArmFull.Fn.M1094
import ArmFull.Fn.M1147
import ArmFull.Fn.M1180

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
def __DecodeT32__seg10 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__728 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__727 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__727 <b 3634) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__728 : Bool)
  then
    (do
      writeReg SEE 3634
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let N := (BitVec.slice __opcode 7 1)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VQRDMLSH_T1enc_A_txt D size Vn Vd N Q M Vm)
      (pure false))
  else
    (do
      let w__730 ← (( do
        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 11 8)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
        then
          (do
            let w__729 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__729 <b 3635) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__730 : Bool)
      then
        (do
          writeReg SEE 3635
          let Q := (BitVec.slice __opcode 28 1)
          let D := (BitVec.slice __opcode 22 1)
          let size := (BitVec.slice __opcode 20 2)
          let Vn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let N := (BitVec.slice __opcode 7 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VQRDMLSH_T2enc_A_txt Q D size Vn Vd N M Vm)
          (pure false))
      else
        (do
          let w__732 ← (( do
            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                       __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                let w__731 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__731 <b 3637) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__732 : Bool)
          then
            (do
              writeReg SEE 3637
              let U := (BitVec.slice __opcode 28 1)
              let D := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 20 2)
              let Vn := (BitVec.slice __opcode 16 4)
              let Vd := (BitVec.slice __opcode 12 4)
              let N := (BitVec.slice __opcode 7 1)
              let Q := (BitVec.slice __opcode 6 1)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VQRSHL_T1enc_A_txt U D size Vn Vd N Q M Vm)
              (pure false))
          else
            (do
              let w__734 ← (( do
                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                           __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 11 9)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 7 6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                then
                  (do
                    let w__733 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__733 <b 3639) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__734 : Bool)
              then
                (do
                  writeReg SEE 3639
                  let U := (BitVec.slice __opcode 28 1)
                  let D := (BitVec.slice __opcode 22 1)
                  let imm6 := (BitVec.slice __opcode 16 6)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let op := (BitVec.slice __opcode 8 1)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VQRSHRN_T1enc_A_txt U D imm6 Vd op M Vm)
                  (pure false))
              else
                (do
                  let w__736 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                               __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 11 9)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__735 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__735 <b 3641) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__736 : Bool)
                  then
                    (do
                      writeReg SEE 3641
                      let U := (BitVec.slice __opcode 28 1)
                      let D := (BitVec.slice __opcode 22 1)
                      let imm6 := (BitVec.slice __opcode 16 6)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let op := (BitVec.slice __opcode 8 1)
                      let L := (BitVec.slice __opcode 7 1)
                      let Q := (BitVec.slice __opcode 6 1)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VQSHL_i_T1enc_A_txt U D imm6 Vd op L Q M Vm)
                      (pure false))
                  else
                    (do
                      let w__738 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31
                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                   __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 11 8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                        then
                          (do
                            let w__737 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__737 <b 3643) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__738 : Bool)
                      then
                        (do
                          writeReg SEE 3643
                          let U := (BitVec.slice __opcode 28 1)
                          let D := (BitVec.slice __opcode 22 1)
                          let size := (BitVec.slice __opcode 20 2)
                          let Vn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let N := (BitVec.slice __opcode 7 1)
                          let Q := (BitVec.slice __opcode 6 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VQSHL_r_T1enc_A_txt U D size Vn Vd N Q M Vm)
                          (pure false))
                      else
                        (do
                          let w__740 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                       __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 11 9)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 7 6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                            then
                              (do
                                let w__739 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__739 <b 3645) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__740 : Bool)
                          then
                            (do
                              writeReg SEE 3645
                              let U := (BitVec.slice __opcode 28 1)
                              let D := (BitVec.slice __opcode 22 1)
                              let imm6 := (BitVec.slice __opcode 16 6)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let op := (BitVec.slice __opcode 8 1)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VQSHRN_T1enc_A_txt U D imm6 Vd op M Vm)
                              (pure false))
                          else
                            (do
                              let w__742 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 11 8)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__741 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__741 <b 3647) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__742 : Bool)
                              then
                                (do
                                  writeReg SEE 3647
                                  let U := (BitVec.slice __opcode 28 1)
                                  let D := (BitVec.slice __opcode 22 1)
                                  let size := (BitVec.slice __opcode 20 2)
                                  let Vn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let N := (BitVec.slice __opcode 7 1)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VQSUB_T1enc_A_txt U D size Vn Vd N Q M Vm)
                                  (pure false))
                              else
                                (do
                                  let w__744 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0x4#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__743 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__743 <b 3649) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__744 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3649
                                      let D := (BitVec.slice __opcode 22 1)
                                      let size := (BitVec.slice __opcode 20 2)
                                      let Vn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let N := (BitVec.slice __opcode 7 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VRADDHN_T1enc_A_txt D size Vn Vd N M Vm)
                                      (pure false))
                                  else
                                    (do
                                      let w__746 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 17 16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 11 9)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__745 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__745 <b 3651) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__746 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3651
                                          let D := (BitVec.slice __opcode 22 1)
                                          let size := (BitVec.slice __opcode 18 2)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let F := (BitVec.slice __opcode 8 1)
                                          let Q := (BitVec.slice __opcode 6 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VRECPE_T1enc_A_txt D size Vd F Q M
                                            Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__748 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 11 8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__747 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__747 <b 3653) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__748 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3653
                                              let D := (BitVec.slice __opcode 22 1)
                                              let sz := (BitVec.slice __opcode 20 1)
                                              let Vn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let N := (BitVec.slice __opcode 7 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VRECPS_T1enc_A_txt D sz Vn Vd N
                                                Q M Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__750 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 11 9)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__749 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__749 <b 3655) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__750 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3655
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 18 2)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let op := (BitVec.slice __opcode 7 2)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VREV16_T1enc_A_txt D size
                                                    Vd op Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__752 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                               __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 11 8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__751 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__751 <b 3657) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__752 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3657
                                                      let U := (BitVec.slice __opcode 28 1)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let size := (BitVec.slice __opcode 20 2)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VRHADD_T1enc_A_txt U D
                                                        size Vn Vd N Q M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__754 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                   __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__753 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__753 <b 3659) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__754 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3659
                                                          let U := (BitVec.slice __opcode 28 1)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 20 2)
                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let N := (BitVec.slice __opcode 7 1)
                                                          let Q := (BitVec.slice __opcode 6 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VRSHL_T1enc_A_txt U
                                                            D size Vn Vd N Q M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__756 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                       __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__755 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__755 <b 3661) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__756 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3661
                                                              let U := (BitVec.slice __opcode 28 1)
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let imm6 :=
                                                                (BitVec.slice __opcode 16 6)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let L := (BitVec.slice __opcode 7 1)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VRSHR_T1enc_A_txt
                                                                U D imm6 Vd L Q M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__758 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 11 6)) == (0b100001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__757 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__757 <b 3663) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__758 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3663
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let imm6 :=
                                                                    (BitVec.slice __opcode 16 6)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VRSHRN_T1enc_A_txt
                                                                    D imm6 Vd M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__760 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 17 16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 9)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 7 7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__759 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__759 <b 3665) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__760 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3665
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 18 2)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let F :=
                                                                        (BitVec.slice __opcode 8 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VRSQRTE_T1enc_A_txt
                                                                        D size Vd F Q M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__762 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__761 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__761 <b 3667) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__762 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3667
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Vn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode 6
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VRSQRTS_T1enc_A_txt
                                                                            D sz Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__764 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                       __opcode 27
                                                                                       23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__763 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__763 <b 3669) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__764 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3669
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 1)
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let imm6 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 6)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VRSRA_T1enc_A_txt
                                                                                U D imm6 Vd L Q M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__766 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__765 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__765 <b 3671) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__766 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3671
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 2)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VRSUBHN_T1enc_A_txt
                                                                                    D size Vn Vd N M
                                                                                    Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__768 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__767 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__767 <b 3673) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__768 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3673
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let imm6 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 6)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let L :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VSHL_i_T1enc_A_txt
                                                                                        D imm6 Vd L
                                                                                        Q M Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__770 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   27
                                                                                                   23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     6)) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__769 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__769 <b 3676) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__770 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3676
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 1)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let imm6 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 6)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VSHLL_T1enc_A_txt
                                                                                            U D imm6
                                                                                            Vd M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__772 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         17
                                                                                                         16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           6)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__771 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__771 <b 3677) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__772 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3677
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  18
                                                                                                  2)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let M :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let Vm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VSHLL_T2enc_A_txt
                                                                                                D
                                                                                                size
                                                                                                Vd M
                                                                                                Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__774 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           27
                                                                                                           23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__773 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__773 <b 3679) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__774 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3679
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      1)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      20
                                                                                                      2)
                                                                                                  let Vn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let Vm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VSHL_r_T1enc_A_txt
                                                                                                    U
                                                                                                    D
                                                                                                    size
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    N
                                                                                                    Q
                                                                                                    M
                                                                                                    Vm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__776 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               27
                                                                                                               23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 8)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__775 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__775 <b 3681) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__776 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3681
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          1)
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let imm6 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          6)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let L :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          7
                                                                                                          1)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          1)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let Vm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VSHR_T1enc_A_txt
                                                                                                        U
                                                                                                        D
                                                                                                        imm6
                                                                                                        Vd
                                                                                                        L
                                                                                                        Q
                                                                                                        M
                                                                                                        Vm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__778 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   6)) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__777 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__777 <b 3683) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__778 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3683
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let imm6 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              6)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let Vm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VSHRN_T1enc_A_txt
                                                                                                            D
                                                                                                            imm6
                                                                                                            Vd
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__780 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__779 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__779 <b 3685) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__780 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3685
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let imm6 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  6)
                                                                                                              let Vd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let L :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  1)
                                                                                                              let Q :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  1)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  1)
                                                                                                              let Vm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_VSLI_T1enc_A_txt
                                                                                                                D
                                                                                                                imm6
                                                                                                                Vd
                                                                                                                L
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__782 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           16)) == (0b110001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               7
                                                                                                                               6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__781 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__781 <b 3687) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__782 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3687
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      2)
                                                                                                                  let M :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      1)
                                                                                                                  let Vm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_VSQRT_T1enc_A_txt
                                                                                                                    D
                                                                                                                    Vd
                                                                                                                    size
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__784 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               27
                                                                                                                               23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__783 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__783 <b 3689) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__784 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3689
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
                                                                                                                          1)
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let imm6 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          6)
                                                                                                                      let Vd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let L :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          7
                                                                                                                          1)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          1)
                                                                                                                      let M :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          1)
                                                                                                                      let Vm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_VSRA_T1enc_A_txt
                                                                                                                        U
                                                                                                                        D
                                                                                                                        imm6
                                                                                                                        Vd
                                                                                                                        L
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__786 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__785 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__785 <b 3691) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__786 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3691
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let imm6 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              6)
                                                                                                                          let Vd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let L :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              1)
                                                                                                                          let Q :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              1)
                                                                                                                          let M :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              1)
                                                                                                                          let Vm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_VSRI_T1enc_A_txt
                                                                                                                            D
                                                                                                                            imm6
                                                                                                                            Vd
                                                                                                                            L
                                                                                                                            Q
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (pure true))))))))))))))))))))))))))))))


end ArmFull.Functions
