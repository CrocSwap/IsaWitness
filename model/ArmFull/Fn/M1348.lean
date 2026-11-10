import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1054
import ArmFull.Fn.M1055
import ArmFull.Fn.M1056
import ArmFull.Fn.M1057
import ArmFull.Fn.M1093
import ArmFull.Fn.M1094
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
def __DecodeA32_Unconditional__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__233 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 11 8)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
    then
      (do
        let w__232 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__232 <b 3620) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__233 : Bool)
  then
    (do
      writeReg SEE 3620
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 18 2)
      let Vd := (BitVec.slice __opcode 12 4)
      let op := (BitVec.slice __opcode 6 2)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VQMOVN_A1enc_A_txt D size Vd op M Vm)
      (pure false))
  else
    (do
      let w__235 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                       __opcode 11 7)) == (0b01111#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
        then
          (do
            let w__234 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__234 <b 3622) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__235 : Bool)
      then
        (do
          writeReg SEE 3622
          let D := (BitVec.slice __opcode 22 1)
          let size := (BitVec.slice __opcode 18 2)
          let Vd := (BitVec.slice __opcode 12 4)
          let Q := (BitVec.slice __opcode 6 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VQNEG_A1enc_A_txt D size Vd Q M Vm)
          (pure false))
      else
        (do
          let w__237 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 11 8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__236 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__236 <b 3624) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__237 : Bool)
          then
            (do
              writeReg SEE 3624
              let D := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 20 2)
              let Vn := (BitVec.slice __opcode 16 4)
              let Vd := (BitVec.slice __opcode 12 4)
              let N := (BitVec.slice __opcode 7 1)
              let Q := (BitVec.slice __opcode 6 1)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VQRDMULH_A1enc_A_txt D size Vn Vd N Q M Vm)
              (pure false))
          else
            (do
              let w__239 ← (( do
                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                             __opcode 11 8)) == (0xD#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                then
                  (do
                    let w__238 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__238 <b 3625) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__239 : Bool)
              then
                (do
                  writeReg SEE 3625
                  let Q := (BitVec.slice __opcode 24 1)
                  let D := (BitVec.slice __opcode 22 1)
                  let size := (BitVec.slice __opcode 20 2)
                  let Vn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let N := (BitVec.slice __opcode 7 1)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VQRDMULH_A2enc_A_txt Q D size Vn Vd N M Vm)
                  (pure false))
              else
                (do
                  let w__241 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 11 8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__240 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__240 <b 3628) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__241 : Bool)
                  then
                    (do
                      writeReg SEE 3628
                      let D := (BitVec.slice __opcode 22 1)
                      let size := (BitVec.slice __opcode 20 2)
                      let Vn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let N := (BitVec.slice __opcode 7 1)
                      let Q := (BitVec.slice __opcode 6 1)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VQRDMLAH_A1enc_A_txt D size Vn Vd N Q M Vm)
                      (pure false))
                  else
                    (do
                      let w__243 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31
                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 11 8)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                        then
                          (do
                            let w__242 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__242 <b 3629) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__243 : Bool)
                      then
                        (do
                          writeReg SEE 3629
                          let Q := (BitVec.slice __opcode 24 1)
                          let D := (BitVec.slice __opcode 22 1)
                          let size := (BitVec.slice __opcode 20 2)
                          let Vn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let N := (BitVec.slice __opcode 7 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VQRDMLAH_A2enc_A_txt Q D size Vn Vd N M Vm)
                          (pure false))
                      else
                        (do
                          let w__245 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__244 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__244 <b 3632) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__245 : Bool)
                          then
                            (do
                              writeReg SEE 3632
                              let D := (BitVec.slice __opcode 22 1)
                              let size := (BitVec.slice __opcode 20 2)
                              let Vn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let N := (BitVec.slice __opcode 7 1)
                              let Q := (BitVec.slice __opcode 6 1)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VQRDMLSH_A1enc_A_txt D size Vn Vd N Q M Vm)
                              (pure false))
                          else
                            (do
                              let w__247 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                         __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 11 8)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__246 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__246 <b 3633) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__247 : Bool)
                              then
                                (do
                                  writeReg SEE 3633
                                  let Q := (BitVec.slice __opcode 24 1)
                                  let D := (BitVec.slice __opcode 22 1)
                                  let size := (BitVec.slice __opcode 20 2)
                                  let Vn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let N := (BitVec.slice __opcode 7 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VQRDMLSH_A2enc_A_txt Q D size Vn Vd N M Vm)
                                  (pure false))
                              else
                                (do
                                  let w__249 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                             __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__248 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__248 <b 3636) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__249 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3636
                                      let U := (BitVec.slice __opcode 24 1)
                                      let D := (BitVec.slice __opcode 22 1)
                                      let size := (BitVec.slice __opcode 20 2)
                                      let Vn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let N := (BitVec.slice __opcode 7 1)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VQRSHL_A1enc_A_txt U D size Vn Vd N Q M
                                        Vm)
                                      (pure false))
                                  else
                                    (do
                                      let w__251 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                 __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 11 9)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 7 6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__250 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__250 <b 3638) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__251 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3638
                                          let U := (BitVec.slice __opcode 24 1)
                                          let D := (BitVec.slice __opcode 22 1)
                                          let imm6 := (BitVec.slice __opcode 16 6)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let op := (BitVec.slice __opcode 8 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VQRSHRN_A1enc_A_txt U D imm6 Vd op
                                            M Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__253 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                     __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 11 9)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__252 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__252 <b 3640) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__253 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3640
                                              let U := (BitVec.slice __opcode 24 1)
                                              let D := (BitVec.slice __opcode 22 1)
                                              let imm6 := (BitVec.slice __opcode 16 6)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let op := (BitVec.slice __opcode 8 1)
                                              let L := (BitVec.slice __opcode 7 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VQSHL_i_A1enc_A_txt U D imm6 Vd
                                                op L Q M Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__255 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                         __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 11 8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__254 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__254 <b 3642) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__255 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3642
                                                  let U := (BitVec.slice __opcode 24 1)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 20 2)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VQSHL_r_A1enc_A_txt U D
                                                    size Vn Vd N Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__257 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 11 9)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 7 6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__256 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__256 <b 3644) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__257 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3644
                                                      let U := (BitVec.slice __opcode 24 1)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let imm6 := (BitVec.slice __opcode 16 6)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let op := (BitVec.slice __opcode 8 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VQSHRN_A1enc_A_txt U D
                                                        imm6 Vd op M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__259 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                 __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__258 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__258 <b 3646) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__259 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3646
                                                          let U := (BitVec.slice __opcode 24 1)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 20 2)
                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let N := (BitVec.slice __opcode 7 1)
                                                          let Q := (BitVec.slice __opcode 6 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VQSUB_A1enc_A_txt U
                                                            D size Vn Vd N Q M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__261 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 11 8)) == (0x4#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__260 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__260 <b 3648) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__261 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3648
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 20 2)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VRADDHN_A1enc_A_txt
                                                                D size Vn Vd N M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__263 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 17 16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 11 9)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__262 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__262 <b 3650) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__263 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3650
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
                                                                  (decode_aarch32_instrs_VRECPE_A1enc_A_txt
                                                                    D size Vd F Q M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__265 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__264 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__264 <b 3652) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__265 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3652
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let Vn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 7 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VRECPS_A1enc_A_txt
                                                                        D sz Vn Vd N Q M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__267 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 11 9)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__266 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__266 <b 3654) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__267 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3654
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              18 2)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let op :=
                                                                            (BitVec.slice __opcode 7
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
                                                                          (decode_aarch32_instrs_VREV16_A1enc_A_txt
                                                                            D size Vd op Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__269 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 23
                                                                                       23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__268 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__268 <b 3656) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__269 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3656
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 24 1)
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
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VRHADD_A1enc_A_txt
                                                                                U D size Vn Vd N Q M
                                                                                Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__271 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__270 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__270 <b 3658) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__271 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3658
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 24 1)
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
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VRSHL_A1enc_A_txt
                                                                                    U D size Vn Vd N
                                                                                    Q M Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__273 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 8)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__272 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__272 <b 3660) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__273 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3660
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          24 1)
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
                                                                                      (decode_aarch32_instrs_VRSHR_A1enc_A_txt
                                                                                        U D imm6 Vd
                                                                                        L Q M Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__275 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   6)) == (0b100001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__274 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__274 <b 3662) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__275 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3662
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
                                                                                          (decode_aarch32_instrs_VRSHRN_A1enc_A_txt
                                                                                            D imm6
                                                                                            Vd M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__277 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         17
                                                                                                         16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           9)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             7
                                                                                                             7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__276 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__276 <b 3664) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__277 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3664
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
                                                                                              let F :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
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
                                                                                              (decode_aarch32_instrs_VRSQRTE_A1enc_A_txt
                                                                                                D
                                                                                                size
                                                                                                Vd F
                                                                                                Q M
                                                                                                Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__279 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__278 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__278 <b 3666) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__279 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3666
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
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
                                                                                                  (decode_aarch32_instrs_VRSQRTS_A1enc_A_txt
                                                                                                    D
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
                                                                                                  let w__281 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               23
                                                                                                               23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__280 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__280 <b 3668) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__281 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3668
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          24
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
                                                                                                      (decode_aarch32_instrs_VRSRA_A1enc_A_txt
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
                                                                                                      let w__283 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   8)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     6
                                                                                                                     6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__282 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__282 <b 3670) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__283 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3670
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
                                                                                                          (decode_aarch32_instrs_VRSUBHN_A1enc_A_txt
                                                                                                            D
                                                                                                            size
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            N
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__285 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__284 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__284 <b 3672) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__285 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3672
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
                                                                                                              (decode_aarch32_instrs_VSHL_i_A1enc_A_txt
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
                                                                                                              let w__287 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           23
                                                                                                                           23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             6)) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__286 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__286 <b 3674) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__287 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3674
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      24
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
                                                                                                                  (decode_aarch32_instrs_VSHLL_A1enc_A_txt
                                                                                                                    U
                                                                                                                    D
                                                                                                                    imm6
                                                                                                                    Vd
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__289 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
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
                                                                                                                        let w__288 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__288 <b 3675) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__289 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3675
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
                                                                                                                      (decode_aarch32_instrs_VSHLL_A2enc_A_txt
                                                                                                                        D
                                                                                                                        size
                                                                                                                        Vd
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (pure true)))))))))))))))))))))))))))))


end ArmFull.Functions
