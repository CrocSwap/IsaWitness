import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0171
import ArmFull.Fn.M1061
import ArmFull.Fn.M1109
import ArmFull.Fn.M1110
import ArmFull.Fn.M1313
import ArmFull.Fn.M1314

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
def __DecodeA64_LoadStore__seg7 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__486 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
    then
      (do
        let w__485 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__485 <b 688) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__486 : Bool)
  then
    (do
      writeReg SEE 688
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let imm9 := (BitVec.slice __opcode 12 9)
      let opc := (BitVec.slice __opcode 22 2)
      let size := (BitVec.slice __opcode 30 2)
      (decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9
        opc size)
      (pure false))
  else
    (do
      let w__488 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
        then
          (do
            let w__487 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__487 <b 689) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__488 : Bool)
      then
        (do
          writeReg SEE 689
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let imm9 := (BitVec.slice __opcode 12 9)
          let opc := (BitVec.slice __opcode 22 2)
          let size := (BitVec.slice __opcode 30 2)
          (decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn
            imm9 opc size)
          (pure false))
      else
        (do
          let w__490 ← (( do
            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1111100110#10 : (BitVec 10))) : Bool) : Bool)
            then
              (do
                let w__489 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__489 <b 716) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__490 : Bool)
          then
            (do
              writeReg SEE 716
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let imm12 := (BitVec.slice __opcode 10 12)
              let opc := (BitVec.slice __opcode 22 2)
              let size := (BitVec.slice __opcode 30 2)
              (decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12
                opc size)
              (pure false))
          else
            (do
              let w__492 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                then
                  (do
                    let w__491 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__491 <b 720) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__492 : Bool)
              then
                (do
                  writeReg SEE 720
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rs := (BitVec.slice __opcode 16 5)
                  let R := (BitVec.slice __opcode 22 1)
                  let A := (BitVec.slice __opcode 23 1)
                  let S := (BitVec.slice __opcode 30 1)
                  (decode_rcwcas_aarch64_instrs_memory_rcw_cas Rt Rn Rs R A S)
                  (pure false))
              else
                (do
                  let w__494 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__493 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__493 <b 721) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__494 : Bool)
                  then
                    (do
                      writeReg SEE 721
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rs := (BitVec.slice __opcode 16 5)
                      let R := (BitVec.slice __opcode 22 1)
                      let A := (BitVec.slice __opcode 23 1)
                      let S := (BitVec.slice __opcode 30 1)
                      (decode_rcwcasp_aarch64_instrs_memory_rcw_cas_128 Rt Rn Rs R A S)
                      (pure false))
                  else
                    (do
                      let w__496 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 15 10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                        then
                          (do
                            let w__495 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__495 <b 722) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__496 : Bool)
                      then
                        (do
                          writeReg SEE 722
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let opc := (BitVec.slice __opcode 12 3)
                          let o3 := (BitVec.slice __opcode 15 1)
                          let Rs := (BitVec.slice __opcode 16 5)
                          let R := (BitVec.slice __opcode 22 1)
                          let A := (BitVec.slice __opcode 23 1)
                          let S := (BitVec.slice __opcode 30 1)
                          (decode_rcwclr_aarch64_instrs_memory_rcw_ld_rcwclr Rt Rn opc o3 Rs R A S)
                          (pure false))
                      else
                        (do
                          let w__498 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 15 10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                            then
                              (do
                                let w__497 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__497 <b 723) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__498 : Bool)
                          then
                            (do
                              writeReg SEE 723
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let opc := (BitVec.slice __opcode 12 3)
                              let o3 := (BitVec.slice __opcode 15 1)
                              let Rt2 := (BitVec.slice __opcode 16 5)
                              let R := (BitVec.slice __opcode 22 1)
                              let A := (BitVec.slice __opcode 23 1)
                              let S := (BitVec.slice __opcode 30 1)
                              (decode_rcwclrp_aarch64_instrs_memory_rcw_ld_128_rcwclrp Rt Rn opc o3
                                Rt2 R A S)
                              (pure false))
                          else
                            (do
                              let w__500 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x59#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__499 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__499 <b 724) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__500 : Bool)
                              then
                                (do
                                  writeReg SEE 724
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Rs := (BitVec.slice __opcode 16 5)
                                  let R := (BitVec.slice __opcode 22 1)
                                  let A := (BitVec.slice __opcode 23 1)
                                  let S := (BitVec.slice __opcode 30 1)
                                  (decode_rcwscas_aarch64_instrs_memory_rcws_cas Rt Rn Rs R A S)
                                  (pure false))
                              else
                                (do
                                  let w__502 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x59#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__501 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__501 <b 725) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__502 : Bool)
                                  then
                                    (do
                                      writeReg SEE 725
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Rs := (BitVec.slice __opcode 16 5)
                                      let R := (BitVec.slice __opcode 22 1)
                                      let A := (BitVec.slice __opcode 23 1)
                                      let S := (BitVec.slice __opcode 30 1)
                                      (decode_rcwscasp_aarch64_instrs_memory_rcws_cas_128 Rt Rn Rs R
                                        A S)
                                      (pure false))
                                  else
                                    (do
                                      let w__504 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__503 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__503 <b 726) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__504 : Bool)
                                      then
                                        (do
                                          writeReg SEE 726
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let opc := (BitVec.slice __opcode 12 3)
                                          let o3 := (BitVec.slice __opcode 15 1)
                                          let Rs := (BitVec.slice __opcode 16 5)
                                          let R := (BitVec.slice __opcode 22 1)
                                          let A := (BitVec.slice __opcode 23 1)
                                          let S := (BitVec.slice __opcode 30 1)
                                          (decode_rcwsclr_aarch64_instrs_memory_rcws_ld_rcwsclr Rt
                                            Rn opc o3 Rs R A S)
                                          (pure false))
                                      else
                                        (do
                                          let w__506 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x59#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__505 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__505 <b 727) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__506 : Bool)
                                          then
                                            (do
                                              writeReg SEE 727
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let opc := (BitVec.slice __opcode 12 3)
                                              let o3 := (BitVec.slice __opcode 15 1)
                                              let Rt2 := (BitVec.slice __opcode 16 5)
                                              let R := (BitVec.slice __opcode 22 1)
                                              let A := (BitVec.slice __opcode 23 1)
                                              let S := (BitVec.slice __opcode 30 1)
                                              (decode_rcwsclrp_aarch64_instrs_memory_rcws_ld_128_rcwsclrp
                                                Rt Rn opc o3 Rt2 R A S)
                                              (pure false))
                                          else
                                            (do
                                              let w__508 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__507 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__507 <b 728) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__508 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 728
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let opc := (BitVec.slice __opcode 12 3)
                                                  let o3 := (BitVec.slice __opcode 15 1)
                                                  let Rs := (BitVec.slice __opcode 16 5)
                                                  let R := (BitVec.slice __opcode 22 1)
                                                  let A := (BitVec.slice __opcode 23 1)
                                                  let S := (BitVec.slice __opcode 30 1)
                                                  (decode_rcwset_aarch64_instrs_memory_rcw_ld_rcwset
                                                    Rt Rn opc o3 Rs R A S)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__510 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__509 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__509 <b 729) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__510 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 729
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let opc := (BitVec.slice __opcode 12 3)
                                                      let o3 := (BitVec.slice __opcode 15 1)
                                                      let Rt2 := (BitVec.slice __opcode 16 5)
                                                      let R := (BitVec.slice __opcode 22 1)
                                                      let A := (BitVec.slice __opcode 23 1)
                                                      let S := (BitVec.slice __opcode 30 1)
                                                      (decode_rcwsetp_aarch64_instrs_memory_rcw_ld_128_rcwsetp
                                                        Rt Rn opc o3 Rt2 R A S)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__512 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__511 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__511 <b 730) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__512 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 730
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let opc := (BitVec.slice __opcode 12 3)
                                                          let o3 := (BitVec.slice __opcode 15 1)
                                                          let Rs := (BitVec.slice __opcode 16 5)
                                                          let R := (BitVec.slice __opcode 22 1)
                                                          let A := (BitVec.slice __opcode 23 1)
                                                          let S := (BitVec.slice __opcode 30 1)
                                                          (decode_rcwsset_aarch64_instrs_memory_rcws_ld_rcwsset
                                                            Rt Rn opc o3 Rs R A S)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__514 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x59#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__513 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__513 <b 731) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__514 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 731
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let opc :=
                                                                (BitVec.slice __opcode 12 3)
                                                              let o3 := (BitVec.slice __opcode 15 1)
                                                              let Rt2 :=
                                                                (BitVec.slice __opcode 16 5)
                                                              let R := (BitVec.slice __opcode 22 1)
                                                              let A := (BitVec.slice __opcode 23 1)
                                                              let S := (BitVec.slice __opcode 30 1)
                                                              (decode_rcwssetp_aarch64_instrs_memory_rcws_ld_128_rcwssetp
                                                                Rt Rn opc o3 Rt2 R A S)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__516 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__515 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__515 <b 732) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__516 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 732
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 12 3)
                                                                  let o3 :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let R :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let A :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_rcwsswp_aarch64_instrs_memory_rcws_swp
                                                                    Rt Rn opc o3 Rs R A S)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__518 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x59#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__517 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__517 <b 733) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__518 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 733
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 12 3)
                                                                      let o3 :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let Rt2 :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let R :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let A :=
                                                                        (BitVec.slice __opcode 23 1)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_rcwsswpp_aarch64_instrs_memory_rcws_swp_128
                                                                        Rt Rn opc o3 Rt2 R A S)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__520 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__519 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__519 <b 734) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__520 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 734
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              12 3)
                                                                          let o3 :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let R :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let A :=
                                                                            (BitVec.slice __opcode
                                                                              23 1)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_rcwswp_aarch64_instrs_memory_rcw_swp
                                                                            Rt Rn opc o3 Rs R A S)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__522 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__521 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__521 <b 735) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__522 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 735
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 3)
                                                                              let o3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rt2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let R :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let A :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 1)
                                                                              (decode_rcwswpp_aarch64_instrs_memory_rcw_swp_128
                                                                                Rt Rn opc o3 Rt2 R A
                                                                                S)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__524 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b11111000101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           14 14)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__523 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__523 <b 743) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__524 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 743
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let option_name :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 3)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  (decode_rprfm_reg_aarch64_instrs_memory_single_general_range
                                                                                    Rt Rn S
                                                                                    option_name Rm
                                                                                    opc size)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__526 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             29 21)) == (0b011001110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             13 10)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__525 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__525 <b 787) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__526 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 787
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let op2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 2)
                                                                                      (decode_setp_aarch64_instrs_memory_mcpymset_set
                                                                                        Rd Rn op2 Rs
                                                                                        sz)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__528 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 29
                                                                                                 21)) == (0b011001110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 13
                                                                                                 10)) == (0x9#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__527 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__527 <b 788) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__528 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 788
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let op2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          (decode_setpn_aarch64_instrs_memory_mcpymset_set
                                                                                            Rd Rn
                                                                                            op2 Rs
                                                                                            sz)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__530 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     29
                                                                                                     21)) == (0b011001110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     13
                                                                                                     10)) == (0x5#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__529 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__529 <b 789) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__530 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 789
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let op2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Rs :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_setpt_aarch64_instrs_memory_mcpymset_set
                                                                                                Rd
                                                                                                Rn
                                                                                                op2
                                                                                                Rs
                                                                                                sz)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__532 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         29
                                                                                                         21)) == (0b011001110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         13
                                                                                                         10)) == (0xD#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__531 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__531 <b 790) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__532 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 790
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let op2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let Rs :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_setptn_aarch64_instrs_memory_mcpymset_set
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    op2
                                                                                                    Rs
                                                                                                    sz)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__534 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             29
                                                                                                             21)) == (0b011101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             13
                                                                                                             10)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__533 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__533 <b 792) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__534 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 792
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let op2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let Rs :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_setgp_aarch64_instrs_memory_mcpymset_setg
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        op2
                                                                                                        Rs
                                                                                                        sz)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__536 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 29
                                                                                                                 21)) == (0b011101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 13
                                                                                                                 10)) == (0x9#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__535 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__535 <b 793) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__536 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 793
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let op2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let Rs :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let sz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_setgpn_aarch64_instrs_memory_mcpymset_setg
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            op2
                                                                                                            Rs
                                                                                                            sz)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__538 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     29
                                                                                                                     21)) == (0b011101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     13
                                                                                                                     10)) == (0x5#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__537 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__537 <b 794) : Bool))))
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
                                                                                                              writeReg SEE 794
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let op2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let Rs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  2)
                                                                                                              (decode_setgpt_aarch64_instrs_memory_mcpymset_setg
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                op2
                                                                                                                Rs
                                                                                                                sz)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__540 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         29
                                                                                                                         21)) == (0b011101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         13
                                                                                                                         10)) == (0xD#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__539 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__539 <b 795) : Bool))))
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
                                                                                                                  writeReg SEE 795
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let op2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let Rs :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let sz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      2)
                                                                                                                  (decode_setgptn_aarch64_instrs_memory_mcpymset_setg
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    op2
                                                                                                                    Rs
                                                                                                                    sz)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__542 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b11011001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__541 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__541 <b 969) : Bool))))
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
                                                                                                                      writeReg SEE 969
                                                                                                                      let Xt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      let Xn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let imm9 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          9)
                                                                                                                      (decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpost
                                                                                                                        Xt
                                                                                                                        Xn
                                                                                                                        imm9)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__544 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11011001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__543 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__543 <b 970) : Bool))))
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
                                                                                                                          writeReg SEE 970
                                                                                                                          let Xt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          let Xn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let imm9 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              9)
                                                                                                                          (decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpre
                                                                                                                            Xt
                                                                                                                            Xn
                                                                                                                            imm9)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__546 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b11011001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__545 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__545 <b 971) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__546 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 971
                                                                                                                              let Xt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let Xn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let imm9 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  9)
                                                                                                                              (decode_st2g_aarch64_instrs_integer_tags_mcsettagpair
                                                                                                                                Xt
                                                                                                                                Xn
                                                                                                                                imm9)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__548 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       31
                                                                                                                                       10)) == (0b1111100000111111100100#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__547 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__547 <b 972) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__548 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 972
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  (decode_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b
                                                                                                                                    Rt
                                                                                                                                    Rn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__550 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11111000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             10)) == (0b101100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__549 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__549 <b 973) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__550 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 973
                                                                                                                                      let Rt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Rs :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      (decode_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv
                                                                                                                                        Rt
                                                                                                                                        Rn
                                                                                                                                        Rs)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__552 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b11111000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b101000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__551 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__551 <b 974) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__552 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 974
                                                                                                                                          let Rt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Rs :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          (decode_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0
                                                                                                                                            Rt
                                                                                                                                            Rn
                                                                                                                                            Rs)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__554 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11011001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     11
                                                                                                                                                     10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__553 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__553 <b 975) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__554 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 975
                                                                                                                                              let Xt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              let Xn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let imm9 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  9)
                                                                                                                                              (decode_stg_aarch64_instrs_integer_tags_mcsettagpost
                                                                                                                                                Xt
                                                                                                                                                Xn
                                                                                                                                                imm9)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__556 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b11011001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__555 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__555 <b 976) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__556 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 976
                                                                                                                                                  let Xt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  let Xn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let imm9 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      9)
                                                                                                                                                  (decode_stg_aarch64_instrs_integer_tags_mcsettagpre
                                                                                                                                                    Xt
                                                                                                                                                    Xn
                                                                                                                                                    imm9)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__558 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b11011001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             11
                                                                                                                                                             10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__557 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__557 <b 977) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__558 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 977
                                                                                                                                                      let Xt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      let Xn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let imm9 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          9)
                                                                                                                                                      (decode_stg_aarch64_instrs_integer_tags_mcsettag
                                                                                                                                                        Xt
                                                                                                                                                        Xn
                                                                                                                                                        imm9)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__560 ← (( do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               31
                                                                                                                                                               10)) == (0b1101100110100000000000#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__559 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__559 <b 978) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__560 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 978
                                                                                                                                                          let Xt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          let Xn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          (decode_stgm_aarch64_instrs_integer_tags_mcsettagarray
                                                                                                                                                            Xt
                                                                                                                                                            Xn)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__562 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   31
                                                                                                                                                                   22)) == (0b0110100010#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__561 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__561 <b 979) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__562 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 979
                                                                                                                                                              let Xt :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              let Xn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Xt2 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  5)
                                                                                                                                                              let simm7 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  15
                                                                                                                                                                  7)
                                                                                                                                                              (decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpost
                                                                                                                                                                Xt
                                                                                                                                                                Xn
                                                                                                                                                                Xt2
                                                                                                                                                                simm7)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__564 ← (( do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       31
                                                                                                                                                                       22)) == (0b0110100110#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__563 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__563 <b 980) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__564 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 980
                                                                                                                                                                  let Xt :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  let Xn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Xt2 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      5)
                                                                                                                                                                  let simm7 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      15
                                                                                                                                                                      7)
                                                                                                                                                                  (decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpre
                                                                                                                                                                    Xt
                                                                                                                                                                    Xn
                                                                                                                                                                    Xt2
                                                                                                                                                                    simm7)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__566 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           31
                                                                                                                                                                           22)) == (0b0110100100#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__565 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__565 <b 981) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__566 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 981
                                                                                                                                                                      let Xt :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      let Xn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          5)
                                                                                                                                                                      let Xt2 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          5)
                                                                                                                                                                      let simm7 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          15
                                                                                                                                                                          7)
                                                                                                                                                                      (decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapair
                                                                                                                                                                        Xt
                                                                                                                                                                        Xn
                                                                                                                                                                        Xt2
                                                                                                                                                                        simm7)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__568 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   29
                                                                                                                                                                                   21)) == (0b011001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     15
                                                                                                                                                                                     13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     11
                                                                                                                                                                                     10)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__567 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__567 <b 982) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__568 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 982
                                                                                                                                                                          let Rt :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let opc2 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              4)
                                                                                                                                                                          let Rt2 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              5)
                                                                                                                                                                          let L :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              1)
                                                                                                                                                                          let size :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              30
                                                                                                                                                                              2)
                                                                                                                                                                          (decode_stilp_aarch64_instrs_memory_ordered_pair_stilp
                                                                                                                                                                            Rt
                                                                                                                                                                            Rn
                                                                                                                                                                            opc2
                                                                                                                                                                            Rt2
                                                                                                                                                                            L
                                                                                                                                                                            size)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
