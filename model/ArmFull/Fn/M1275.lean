import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1048
import ArmFull.Fn.M1049
import ArmFull.Fn.M1090
import ArmFull.Fn.M1091
import ArmFull.Fn.M1092
import ArmFull.Fn.M1143
import ArmFull.Fn.M1144

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
def __DecodeT32__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__490 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
               __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                 __opcode 11 8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
    then
      (do
        let w__489 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__489 <b 3396) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__490 : Bool)
  then
    (do
      writeReg SEE 3396
      let U := (BitVec.slice __opcode 28 1)
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let N := (BitVec.slice __opcode 7 1)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VCGE_r_T1enc_A_txt U D size Vn Vd N Q M Vm)
      (pure false))
  else
    (do
      let w__492 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__491 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__491 <b 3397) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__492 : Bool)
      then
        (do
          writeReg SEE 3397
          let D := (BitVec.slice __opcode 22 1)
          let sz := (BitVec.slice __opcode 20 1)
          let Vn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let N := (BitVec.slice __opcode 7 1)
          let Q := (BitVec.slice __opcode 6 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VCGE_r_T2enc_A_txt D sz Vn Vd N Q M Vm)
          (pure false))
      else
        (do
          let w__494 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 9 7)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
            then
              (do
                let w__493 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__493 <b 3399) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__494 : Bool)
          then
            (do
              writeReg SEE 3399
              let D := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 18 2)
              let Vd := (BitVec.slice __opcode 12 4)
              let F := (BitVec.slice __opcode 10 1)
              let Q := (BitVec.slice __opcode 6 1)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VCGT_i_T1enc_A_txt D size Vd F Q M Vm)
              (pure false))
          else
            (do
              let w__496 ← (( do
                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                           __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                             __opcode 11 8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                then
                  (do
                    let w__495 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__495 <b 3402) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__496 : Bool)
              then
                (do
                  writeReg SEE 3402
                  let U := (BitVec.slice __opcode 28 1)
                  let D := (BitVec.slice __opcode 22 1)
                  let size := (BitVec.slice __opcode 20 2)
                  let Vn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let N := (BitVec.slice __opcode 7 1)
                  let Q := (BitVec.slice __opcode 6 1)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VCGT_r_T1enc_A_txt U D size Vn Vd N Q M Vm)
                  (pure false))
              else
                (do
                  let w__498 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                 __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__497 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__497 <b 3403) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__498 : Bool)
                  then
                    (do
                      writeReg SEE 3403
                      let D := (BitVec.slice __opcode 22 1)
                      let sz := (BitVec.slice __opcode 20 1)
                      let Vn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let N := (BitVec.slice __opcode 7 1)
                      let Q := (BitVec.slice __opcode 6 1)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VCGT_r_T2enc_A_txt D sz Vn Vd N Q M Vm)
                      (pure false))
                  else
                    (do
                      let w__500 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 9 7)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                        then
                          (do
                            let w__499 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__499 <b 3405) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__500 : Bool)
                      then
                        (do
                          writeReg SEE 3405
                          let D := (BitVec.slice __opcode 22 1)
                          let size := (BitVec.slice __opcode 18 2)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let F := (BitVec.slice __opcode 10 1)
                          let Q := (BitVec.slice __opcode 6 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VCLE_i_T1enc_A_txt D size Vd F Q M Vm)
                          (pure false))
                      else
                        (do
                          let w__502 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 11 7)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                            then
                              (do
                                let w__501 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__501 <b 3407) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__502 : Bool)
                          then
                            (do
                              writeReg SEE 3407
                              let D := (BitVec.slice __opcode 22 1)
                              let size := (BitVec.slice __opcode 18 2)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let Q := (BitVec.slice __opcode 6 1)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VCLS_T1enc_A_txt D size Vd Q M Vm)
                              (pure false))
                          else
                            (do
                              let w__504 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 9 7)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__503 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__503 <b 3409) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__504 : Bool)
                              then
                                (do
                                  writeReg SEE 3409
                                  let D := (BitVec.slice __opcode 22 1)
                                  let size := (BitVec.slice __opcode 18 2)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let F := (BitVec.slice __opcode 10 1)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VCLT_i_T1enc_A_txt D size Vd F Q M Vm)
                                  (pure false))
                              else
                                (do
                                  let w__506 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                   __opcode 11 7)) == (0b01001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__505 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__505 <b 3411) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__506 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3411
                                      let D := (BitVec.slice __opcode 22 1)
                                      let size := (BitVec.slice __opcode 18 2)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VCLZ_T1enc_A_txt D size Vd Q M Vm)
                                      (pure false))
                                  else
                                    (do
                                      let w__508 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 21 16)) == (0b110100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__507 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__507 <b 3414) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__508 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3414
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let size := (BitVec.slice __opcode 8 2)
                                          let E := (BitVec.slice __opcode 7 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VCMP_T1enc_A_txt D Vd size E M Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__510 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 21 16)) == (0b110101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 11 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                         __opcode 6 0)) == (0b1000000#7 : (BitVec 7)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__509 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__509 <b 3415) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__510 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3415
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let size := (BitVec.slice __opcode 8 2)
                                              let E := (BitVec.slice __opcode 7 1)
                                              if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 3)])) != 0#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_VCMP_T2enc_A_txt D Vd size
                                                    E))
                                              (pure false))
                                          else
                                            (do
                                              let w__512 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                               __opcode 11 7)) == (0b01010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__511 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__511 <b 3417) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__512 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3417
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 18 2)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VCNT_T1enc_A_txt D size Vd
                                                    Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__514 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                               __opcode 21 17)) == (0b11001#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 11 9)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__513 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__513 <b 3419) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__514 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3419
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let op := (BitVec.slice __opcode 16 1)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let sz := (BitVec.slice __opcode 8 1)
                                                      let T := (BitVec.slice __opcode 7 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VCVTB_T1enc_A_txt D op
                                                        Vd sz T M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__516 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 21 16)) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 11 9)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 7 6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__515 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__515 <b 3421) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__516 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3421
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 8 2)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VCVT_ds_T1enc_A_txt
                                                            D Vd size M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__518 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 11 9)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 7 6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__517 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__517 <b 3423) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__518 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3423
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 18 2)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let op := (BitVec.slice __opcode 8 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VCVT_hs_T1enc_A_txt
                                                                D size Vd op M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__520 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 17 16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 11 9)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__519 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__519 <b 3425) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__520 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3425
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 18 2)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 7 2)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VCVT_is_T1enc_A_txt
                                                                    D size Vd op Q M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__522 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 21 19)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__521 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__521 <b 3427) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__522 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3427
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let opc2 :=
                                                                        (BitVec.slice __opcode 16 3)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 8 2)
                                                                      let op :=
                                                                        (BitVec.slice __opcode 7 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VCVT_iv_T1enc_A_txt
                                                                        D opc2 Vd size op M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__524 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                   __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 10)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__523 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__523 <b 3429) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__524 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3429
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              28 1)
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let imm6 :=
                                                                            (BitVec.slice __opcode
                                                                              16 6)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let op :=
                                                                            (BitVec.slice __opcode 8
                                                                              2)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode 6
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VCVT_xs_T1enc_A_txt
                                                                            U D imm6 Vd op Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__526 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       19)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 17
                                                                                         17)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__525 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__525 <b 3431) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__526 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3431
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let sf :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 2)
                                                                              let sx :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let i :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VCVT_xv_T1enc_A_txt
                                                                                D op U Vd sf sx i
                                                                                imm4)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__528 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__527 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__527 <b 3433) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__528 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3433
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 2)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VDIV_T1enc_A_txt
                                                                                    D Vn Vd size N M
                                                                                    Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__530 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 8)) == (0xB#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   6
                                                                                                   6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   0)) == (0b10000#5 : (BitVec 5))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__529 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__529 <b 3435) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__530 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3435
                                                                                      let B :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let E :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 3)])) != 0#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_aarch32_instrs_VDUP_r_T1enc_A_txt
                                                                                            B Q Vd
                                                                                            Rt D E))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__532 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     7)) == (0b11000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__531 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__531 <b 3437) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__532 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3437
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let imm4 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 1)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VDUP_s_T1enc_A_txt
                                                                                            D imm4
                                                                                            Vd Q M
                                                                                            Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__534 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__533 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__533 <b 3439) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__534 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3439
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
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
                                                                                              (decode_aarch32_instrs_VEOR_T1enc_A_txt
                                                                                                D Vn
                                                                                                Vd N
                                                                                                Q M
                                                                                                Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__536 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__535 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__535 <b 3441) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__536 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3441
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
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
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
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
                                                                                                  (decode_aarch32_instrs_VEXT_T1enc_A_txt
                                                                                                    D
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    imm4
                                                                                                    N
                                                                                                    Q
                                                                                                    M
                                                                                                    Vm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__538 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__537 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__537 <b 3444) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__538 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3444
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let op :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          21
                                                                                                          1)
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          20
                                                                                                          1)
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
                                                                                                      (decode_aarch32_instrs_VFMA_T1enc_A_txt
                                                                                                        D
                                                                                                        op
                                                                                                        sz
                                                                                                        Vn
                                                                                                        Vd
                                                                                                        N
                                                                                                        Q
                                                                                                        M
                                                                                                        Vm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__540 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__539 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__539 <b 3445) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__540 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3445
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
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
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              2)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              1)
                                                                                                          let op :=
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
                                                                                                          (decode_aarch32_instrs_VFMA_T2enc_A_txt
                                                                                                            D
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            size
                                                                                                            N
                                                                                                            op
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__542 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__541 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__541 <b 3447) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__542 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3447
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
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
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  2)
                                                                                                              let N :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  1)
                                                                                                              let op :=
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
                                                                                                              (decode_aarch32_instrs_VFNMA_T1enc_A_txt
                                                                                                                D
                                                                                                                Vn
                                                                                                                Vd
                                                                                                                size
                                                                                                                N
                                                                                                                op
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__544 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           27
                                                                                                                           23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               8
                                                                                                                               8)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__543 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__543 <b 3449) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__544 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3449
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
                                                                                                                  let op :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      9
                                                                                                                      1)
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
                                                                                                                  (decode_aarch32_instrs_VHADD_T1enc_A_txt
                                                                                                                    U
                                                                                                                    D
                                                                                                                    size
                                                                                                                    Vn
                                                                                                                    Vd
                                                                                                                    op
                                                                                                                    N
                                                                                                                    Q
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (pure true))))))))))))))))))))))))))))


end ArmFull.Functions
