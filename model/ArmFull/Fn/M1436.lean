import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1057
import ArmFull.Fn.M1058
import ArmFull.Fn.M1059
import ArmFull.Fn.M1147
import ArmFull.Fn.M1288
import ArmFull.Fn.M1289
import ArmFull.Fn.M1290

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
def __DecodeA32_Unconditional__seg5 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__291 ← (( do
    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                 __opcode 11 8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
    then
      (do
        let w__290 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__290 <b 3678) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__291 : Bool)
  then
    (do
      writeReg SEE 3678
      let U := (BitVec.slice __opcode 24 1)
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let N := (BitVec.slice __opcode 7 1)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VSHL_r_A1enc_A_txt U D size Vn Vd N Q M Vm)
      (pure false))
  else
    (do
      let w__293 ← (( do
        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 11 8)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__292 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__292 <b 3680) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__293 : Bool)
      then
        (do
          writeReg SEE 3680
          let U := (BitVec.slice __opcode 24 1)
          let D := (BitVec.slice __opcode 22 1)
          let imm6 := (BitVec.slice __opcode 16 6)
          let Vd := (BitVec.slice __opcode 12 4)
          let L := (BitVec.slice __opcode 7 1)
          let Q := (BitVec.slice __opcode 6 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VSHR_A1enc_A_txt U D imm6 Vd L Q M Vm)
          (pure false))
      else
        (do
          let w__295 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 11 6)) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__294 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__294 <b 3682) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__295 : Bool)
          then
            (do
              writeReg SEE 3682
              let D := (BitVec.slice __opcode 22 1)
              let imm6 := (BitVec.slice __opcode 16 6)
              let Vd := (BitVec.slice __opcode 12 4)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VSHRN_A1enc_A_txt D imm6 Vd M Vm)
              (pure false))
          else
            (do
              let w__297 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 11 8)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__296 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__296 <b 3684) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__297 : Bool)
              then
                (do
                  writeReg SEE 3684
                  let D := (BitVec.slice __opcode 22 1)
                  let imm6 := (BitVec.slice __opcode 16 6)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let L := (BitVec.slice __opcode 7 1)
                  let Q := (BitVec.slice __opcode 6 1)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VSLI_A1enc_A_txt D imm6 Vd L Q M Vm)
                  (pure false))
              else
                (do
                  let w__299 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                 __opcode 11 8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__298 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__298 <b 3688) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__299 : Bool)
                  then
                    (do
                      writeReg SEE 3688
                      let U := (BitVec.slice __opcode 24 1)
                      let D := (BitVec.slice __opcode 22 1)
                      let imm6 := (BitVec.slice __opcode 16 6)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let L := (BitVec.slice __opcode 7 1)
                      let Q := (BitVec.slice __opcode 6 1)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VSRA_A1enc_A_txt U D imm6 Vd L Q M Vm)
                      (pure false))
                  else
                    (do
                      let w__301 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 11 8)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__300 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__300 <b 3690) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__301 : Bool)
                      then
                        (do
                          writeReg SEE 3690
                          let D := (BitVec.slice __opcode 22 1)
                          let imm6 := (BitVec.slice __opcode 16 6)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let L := (BitVec.slice __opcode 7 1)
                          let Q := (BitVec.slice __opcode 6 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VSRI_A1enc_A_txt D imm6 Vd L Q M Vm)
                          (pure false))
                      else
                        (do
                          let w__303 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 11 8)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                            then
                              (do
                                let w__302 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__302 <b 3692) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__303 : Bool)
                          then
                            (do
                              writeReg SEE 3692
                              let D := (BitVec.slice __opcode 22 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let size := (BitVec.slice __opcode 10 2)
                              let index_align := (BitVec.slice __opcode 4 4)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VST1_1_A1enc_A_txt D Rn Vd size index_align Rm)
                              (pure false))
                          else
                            (do
                              let w__305 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 11 8)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__304 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__304 <b 3693) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__305 : Bool)
                              then
                                (do
                                  writeReg SEE 3693
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let size := (BitVec.slice __opcode 10 2)
                                  let index_align := (BitVec.slice __opcode 4 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VST1_1_A2enc_A_txt D Rn Vd size index_align
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__307 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__306 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__306 <b 3694) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__307 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3694
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 10 2)
                                      let index_align := (BitVec.slice __opcode 4 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VST1_1_A3enc_A_txt D Rn Vd size
                                        index_align Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__309 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__308 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__308 <b 3698) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__309 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3698
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let itype := (BitVec.slice __opcode 8 4)
                                          let size := (BitVec.slice __opcode 6 2)
                                          let align := (BitVec.slice __opcode 4 2)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VST1_m_A1enc_A_txt D Rn Vd itype
                                            size align Rm)
                                          (pure false))
                                      else
                                        (do
                                          let w__311 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__310 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__310 <b 3699) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__311 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3699
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let itype := (BitVec.slice __opcode 8 4)
                                              let size := (BitVec.slice __opcode 6 2)
                                              let align := (BitVec.slice __opcode 4 2)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VST1_m_A2enc_A_txt D Rn Vd
                                                itype size align Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__313 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__312 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__312 <b 3700) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__313 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3700
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let itype := (BitVec.slice __opcode 8 4)
                                                  let size := (BitVec.slice __opcode 6 2)
                                                  let align := (BitVec.slice __opcode 4 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VST1_m_A3enc_A_txt D Rn Vd
                                                    itype size align Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__315 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__314 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__314 <b 3701) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__315 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3701
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let itype := (BitVec.slice __opcode 8 4)
                                                      let size := (BitVec.slice __opcode 6 2)
                                                      let align := (BitVec.slice __opcode 4 2)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VST1_m_A4enc_A_txt D Rn
                                                        Vd itype size align Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__317 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 11 8)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__316 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__316 <b 3706) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__317 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3706
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 10 2)
                                                          let index_align :=
                                                            (BitVec.slice __opcode 4 4)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VST2_1_A1enc_A_txt
                                                            D Rn Vd size index_align Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__319 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 11 8)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__318 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__318 <b 3707) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__319 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3707
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let size :=
                                                                (BitVec.slice __opcode 10 2)
                                                              let index_align :=
                                                                (BitVec.slice __opcode 4 4)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VST2_1_A2enc_A_txt
                                                                D Rn Vd size index_align Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__321 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 11 8)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__320 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__320 <b 3708) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__321 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3708
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let index_align :=
                                                                    (BitVec.slice __opcode 4 4)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VST2_1_A3enc_A_txt
                                                                    D Rn Vd size index_align Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__323 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 11 9)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__322 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__322 <b 3712) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__323 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3712
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let itype :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 6 2)
                                                                      let align :=
                                                                        (BitVec.slice __opcode 4 2)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VST2_m_A1enc_A_txt
                                                                        D Rn Vd itype size align Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__325 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__324 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__324 <b 3713) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__325 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3713
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let itype :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let size :=
                                                                            (BitVec.slice __opcode 6
                                                                              2)
                                                                          let align :=
                                                                            (BitVec.slice __opcode 4
                                                                              2)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VST2_m_A2enc_A_txt
                                                                            D Rn Vd itype size align
                                                                            Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__327 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__326 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__326 <b 3716) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__327 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3716
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 2)
                                                                              let index_align :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VST3_1_A1enc_A_txt
                                                                                D Rn Vd size
                                                                                index_align Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__329 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__328 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__328 <b 3717) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__329 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3717
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 2)
                                                                                  let index_align :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VST3_1_A2enc_A_txt
                                                                                    D Rn Vd size
                                                                                    index_align Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__331 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__330 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__330 <b 3718) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__331 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3718
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 2)
                                                                                      let index_align :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VST3_1_A3enc_A_txt
                                                                                        D Rn Vd size
                                                                                        index_align
                                                                                        Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__333 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   9)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__332 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__332 <b 3722) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__333 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3722
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let itype :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 2)
                                                                                          let align :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VST3_m_A1enc_A_txt
                                                                                            D Rn Vd
                                                                                            itype
                                                                                            size
                                                                                            align Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__335 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__334 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__334 <b 3724) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__335 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3724
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Rn :=
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
                                                                                                  10
                                                                                                  2)
                                                                                              let index_align :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VST4_1_A1enc_A_txt
                                                                                                D Rn
                                                                                                Vd
                                                                                                size
                                                                                                index_align
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__337 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__336 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__336 <b 3725) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__337 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3725
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Rn :=
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
                                                                                                      10
                                                                                                      2)
                                                                                                  let index_align :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VST4_1_A2enc_A_txt
                                                                                                    D
                                                                                                    Rn
                                                                                                    Vd
                                                                                                    size
                                                                                                    index_align
                                                                                                    Rm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__339 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__338 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__338 <b 3726) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__339 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3726
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Rn :=
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
                                                                                                          10
                                                                                                          2)
                                                                                                      let index_align :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          4)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VST4_1_A3enc_A_txt
                                                                                                        D
                                                                                                        Rn
                                                                                                        Vd
                                                                                                        size
                                                                                                        index_align
                                                                                                        Rm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__341 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   9)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__340 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__340 <b 3730) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__341 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3730
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let itype :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              2)
                                                                                                          let align :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VST4_m_A1enc_A_txt
                                                                                                            D
                                                                                                            Rn
                                                                                                            Vd
                                                                                                            itype
                                                                                                            size
                                                                                                            align
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__343 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__342 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__342 <b 3738) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__343 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3738
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
                                                                                                              (decode_aarch32_instrs_VSUB_f_A1enc_A_txt
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
                                                                                                              let w__345 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
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
                                                                                                                    let w__344 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__344 <b 3742) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__345 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3742
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
                                                                                                                  (decode_aarch32_instrs_VSUBHN_A1enc_A_txt
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
                                                                                                                  let w__347 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__346 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__346 <b 3744) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__347 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3744
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
                                                                                                                      (decode_aarch32_instrs_VSUB_i_A1enc_A_txt
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
                                                                                                                      let w__349 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   23
                                                                                                                                   23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     9)) == (0b001#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       6
                                                                                                                                       6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__348 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__348 <b 3746) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__349 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3746
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
                                                                                                                              8
                                                                                                                              1)
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
                                                                                                                          (decode_aarch32_instrs_VSUBL_A1enc_A_txt
                                                                                                                            U
                                                                                                                            D
                                                                                                                            size
                                                                                                                            Vn
                                                                                                                            Vd
                                                                                                                            op
                                                                                                                            N
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__351 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         17
                                                                                                                                         16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           7)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__350 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__350 <b 3748) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__351 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3748
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
                                                                                                                              (decode_aarch32_instrs_VSWP_A1enc_A_txt
                                                                                                                                D
                                                                                                                                size
                                                                                                                                Vd
                                                                                                                                Q
                                                                                                                                M
                                                                                                                                Vm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__353 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__352 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__352 <b 3750) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__353 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3750
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
                                                                                                                                  let len :=
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
                                                                                                                                  (decode_aarch32_instrs_VTBL_A1enc_A_txt
                                                                                                                                    D
                                                                                                                                    Vn
                                                                                                                                    Vd
                                                                                                                                    len
                                                                                                                                    N
                                                                                                                                    op
                                                                                                                                    M
                                                                                                                                    Vm)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__355 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 17
                                                                                                                                                 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   11
                                                                                                                                                   7)) == (0b00001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__354 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__354 <b 3752) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__355 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3752
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
                                                                                                                                      (decode_aarch32_instrs_VTRN_A1enc_A_txt
                                                                                                                                        D
                                                                                                                                        size
                                                                                                                                        Vd
                                                                                                                                        Q
                                                                                                                                        M
                                                                                                                                        Vm)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
