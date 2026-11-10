import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0214
import ArmFull.Fn.M0236
import ArmFull.Fn.M0242
import ArmFull.Fn.M0579
import ArmFull.Fn.M0839
import ArmFull.Fn.M0842
import ArmFull.Fn.M0853
import ArmFull.Fn.M1059
import ArmFull.Fn.M1075
import ArmFull.Fn.M1290
import ArmFull.Fn.M1291

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
def __DecodeT32__seg12 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__854 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 11 7)) == (0b00011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
    then
      (do
        let w__853 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__853 <b 3759) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__854 : Bool)
  then
    (do
      writeReg SEE 3759
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 18 2)
      let Vd := (BitVec.slice __opcode 12 4)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VZIP_T1enc_A_txt D size Vd Q M Vm)
      (pure false))
  else
    (do
      let w__856 ← (( do
        if (((__opcode == 0b11110011101011111000000000000010#32) : Bool) : Bool)
        then
          (do
            let w__855 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__855 <b 3762) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__856 : Bool)
      then
        (do
          writeReg SEE 3762
          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 11)])) != 0#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_WFE_T2enc_A_txt ()))
          (pure false))
      else
        (do
          let w__858 ← (( do
            if (((__opcode == 0b11110011101011111000000000000011#32) : Bool) : Bool)
            then
              (do
                let w__857 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__857 <b 3765) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__858 : Bool)
          then
            (do
              writeReg SEE 3765
              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 11)])) != 0#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_WFI_T2enc_A_txt ()))
              (pure false))
          else
            (do
              let w__860 ← (( do
                if (((__opcode == 0b11110011101011111000000000000001#32) : Bool) : Bool)
                then
                  (do
                    let w__859 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__859 <b 3768) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__860 : Bool)
              then
                (do
                  writeReg SEE 3768
                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 11)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_YIELD_T2enc_A_txt ()))
                  (pure false))
              else
                (do
                  let w__862 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb __opcode 31 11)) == (0b111100111010111110000#21 : (BitVec 21))) : Bool) : Bool)
                    then
                      (do
                        let w__861 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__861 <b 3771) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__862 : Bool)
                  then
                    (do
                      writeReg SEE 3771
                      let imod := (BitVec.slice __opcode 9 2)
                      let M := (BitVec.slice __opcode 8 1)
                      let A := (BitVec.slice __opcode 7 1)
                      let I := (BitVec.slice __opcode 6 1)
                      let F := (BitVec.slice __opcode 5 1)
                      let mode := (BitVec.slice __opcode 0 5)
                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 11)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_CPS_T2enc_AS_txt imod M A I F mode))
                      (pure false))
                  else
                    (do
                      let w__864 ← (( do
                        if (((__opcode == 0b11110011110111101000111100000000#32) : Bool) : Bool)
                        then
                          (do
                            let w__863 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__863 <b 3773) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__864 : Bool)
                      then
                        (do
                          writeReg SEE 3773
                          if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 19)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 1#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_ERET_T1enc_A_txt ()))
                          (pure false))
                      else
                        (do
                          let w__866 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xF7E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 15 12)) == (0x8#4 : (BitVec 4)))) : Bool) : Bool)
                            then
                              (do
                                let w__865 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__865 <b 3775) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__866 : Bool)
                          then
                            (do
                              writeReg SEE 3775
                              let imm4 := (BitVec.slice __opcode 16 4)
                              let imm12 := (BitVec.slice __opcode 0 12)
                              (decode_aarch32_instrs_HVC_T1enc_A_txt imm4 imm12)
                              (pure false))
                          else
                            (do
                              let w__868 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11110011111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                           __opcode 19 12)) == (0xF8#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                           __opcode 7 0)) == (0x00#8 : (BitVec 8))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__867 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__867 <b 3779) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__868 : Bool)
                              then
                                (do
                                  writeReg SEE 3779
                                  let R := (BitVec.slice __opcode 20 1)
                                  let Rd := (BitVec.slice __opcode 8 4)
                                  if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 4)])) != 0#1)) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_MRS_T1enc_AS_txt R Rd))
                                  (pure false))
                              else
                                (do
                                  let w__870 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11110011111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 15 12)) == (0x8#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 7 5)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 3 0)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__869 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__869 <b 3781) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__870 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3781
                                      let R := (BitVec.slice __opcode 20 1)
                                      let M1 := (BitVec.slice __opcode 16 4)
                                      let Rd := (BitVec.slice __opcode 8 4)
                                      let M := (BitVec.slice __opcode 4 1)
                                      if (((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 13)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 3)])) != 0#1)) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_MRS_br_T1enc_AS_txt R M1 Rd M))
                                      (pure false))
                                  else
                                    (do
                                      let w__872 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11110011100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0x8#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 7 5)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 3 0)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__871 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__871 <b 3783) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__872 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3783
                                          let R := (BitVec.slice __opcode 20 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let M1 := (BitVec.slice __opcode 8 4)
                                          let M := (BitVec.slice __opcode 4 1)
                                          if (((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 13)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 3)])) != 0#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_MSR_br_T1enc_AS_txt R Rn M1 M))
                                          (pure false))
                                      else
                                        (do
                                          let w__874 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b11110011100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 15 12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                       __opcode 7 0)) == (0x00#8 : (BitVec 8))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__873 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__873 <b 3786) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__874 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3786
                                              let R := (BitVec.slice __opcode 20 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let mask := (BitVec.slice __opcode 8 4)
                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 13)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 4)])) != 0#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_MSR_r_T1enc_AS_txt R Rn
                                                    mask))
                                              (pure false))
                                          else
                                            (do
                                              let w__876 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                         __opcode 31 22)) == (0b1110100000#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                           __opcode 15 0)) == (0xC000#16 : (BitVec 16))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__875 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__875 <b 3788) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__876 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3788
                                                  let W := (BitVec.slice __opcode 21 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  if ((((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 14)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 13)])) != 0#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_RFE_T1enc_AS_txt W Rn))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__878 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                             __opcode 31 22)) == (0b1110100110#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                               __opcode 15 0)) == (0xC000#16 : (BitVec 16))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__877 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__877 <b 3789) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__878 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3789
                                                      let W := (BitVec.slice __opcode 21 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      if ((((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             14)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 13)])) != 0#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_RFE_T2enc_AS_txt W
                                                            Rn))
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__880 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xF7F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                 __opcode 15 0)) == (0x8000#16 : (BitVec 16)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__879 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__879 <b 3791) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__880 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3791
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 11)])) != 0#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_SMC_T1enc_AS_txt
                                                                imm4))
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__882 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                     __opcode 31 22)) == (0b1110100000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                     __opcode 20 5)) == (0x6E00#16 : (BitVec 16)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__881 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__881 <b 3793) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__882 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3793
                                                              let W := (BitVec.slice __opcode 21 1)
                                                              let mode :=
                                                                (BitVec.slice __opcode 0 5)
                                                              if (((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 13)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_SRS_T1enc_AS_txt
                                                                    W mode))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__884 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                         __opcode 31 22)) == (0b1110100110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                         __opcode 20 5)) == (0x6E00#16 : (BitVec 16)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__883 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__883 <b 3794) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__884 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3794
                                                                  let W :=
                                                                    (BitVec.slice __opcode 21 1)
                                                                  let mode :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  if (((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 7)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 13)])) != 0#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_SRS_T2enc_AS_txt
                                                                        W mode))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__886 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xEEF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 11 0)) == (0xA10#12 : (BitVec 12)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__885 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__885 <b 3797) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__886 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3797
                                                                      let reg :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 3)])) != 0#1)) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_aarch32_instrs_VMRS_T1enc_AS_txt
                                                                            reg Rt))
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__888 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xEEE#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 0)) == (0xA10#12 : (BitVec 12)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__887 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__887 <b 3799) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__888 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3799
                                                                          let reg :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 3)])) != 0#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_VMSR_T1enc_AS_txt
                                                                                reg Rt))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__890 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                         __opcode 17
                                                                                         16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 6)) == (0b001101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__889 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__889 <b 3801) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__890 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3801
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 2)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_AESD_T1enc_A_txt
                                                                                D size Vd M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__892 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 6)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__891 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__891 <b 3803) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__892 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3803
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 18 2)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_AESE_T1enc_A_txt
                                                                                    D size Vd M Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__894 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 17
                                                                                                 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   6)) == (0b001111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__893 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__893 <b 3805) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__894 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3805
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          18 2)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_AESIMC_T1enc_A_txt
                                                                                        D size Vd M
                                                                                        Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__896 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     17
                                                                                                     16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       6)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__895 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__895 <b 3807) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__896 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3807
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              18 2)
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
                                                                                          (decode_aarch32_instrs_AESMC_T1enc_A_txt
                                                                                            D size
                                                                                            Vd M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__898 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b11111010110#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       7
                                                                                                       6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__897 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__897 <b 3809) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__898 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3809
                                                                                              let C :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  20
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  2)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_CRC32_T1enc_A_txt
                                                                                                C Rn
                                                                                                Rd
                                                                                                sz
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__900 ← (( do
                                                                                                if (((__opcode == 0b11110111100011111000000000000001#32) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__899 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__899 <b 3810) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__900 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3810
                                                                                                  (decode_aarch32_instrs_DCPS1_T1enc_A_txt
                                                                                                    ())
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__902 ← (( do
                                                                                                    if (((__opcode == 0b11110111100011111000000000000010#32) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__901 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__901 <b 3811) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__902 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3811
                                                                                                      (decode_aarch32_instrs_DCPS2_T1enc_A_txt
                                                                                                        ())
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__904 ← (( do
                                                                                                        if (((__opcode == 0b11110111100011111000000000000011#32) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__903 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__903 <b 3812) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__904 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3812
                                                                                                          (decode_aarch32_instrs_DCPS3_T1enc_A_txt
                                                                                                            ())
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__906 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     0)) == (0xFAF#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__905 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__905 <b 3816) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__906 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3816
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         3)])) != 1#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_LDA_T1enc_A_txt
                                                                                                                    Rn
                                                                                                                    Rt))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__908 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         0)) == (0xF8F#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__907 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__907 <b 3818) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__908 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3818
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Rt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             3)])) != 1#1)) : Bool)
                                                                                                                  then
                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                      ()))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      (decode_aarch32_instrs_LDAB_T1enc_A_txt
                                                                                                                        Rn
                                                                                                                        Rt))
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__910 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             0)) == (0xFEF#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__909 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__909 <b 3820) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__910 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3820
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 3)])) != 1#1)) : Bool)
                                                                                                                      then
                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                          ()))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          (decode_aarch32_instrs_LDAEX_T1enc_A_txt
                                                                                                                            Rn
                                                                                                                            Rt))
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (pure true)))))))))))))))))))))))))))))


end ArmFull.Functions
