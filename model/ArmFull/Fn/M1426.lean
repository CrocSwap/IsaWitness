import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1109
import ArmFull.Fn.M1298
import ArmFull.Fn.M1299
import ArmFull.Fn.M1300

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
def __DecodeA64_LoadStore__seg3 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__205 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__204 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__204 <b 548) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__205 : Bool)
  then
    (do
      writeReg SEE 548
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let opc := (BitVec.slice __opcode 12 3)
      let Rs := (BitVec.slice __opcode 16 5)
      let R := (BitVec.slice __opcode 22 1)
      let A := (BitVec.slice __opcode 23 1)
      let size := (BitVec.slice __opcode 30 2)
      (decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size)
      (pure false))
  else
    (do
      let w__207 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                 __opcode 29 10)) == (0x35061#20 : (BitVec 20)))) : Bool) : Bool)
        then
          (do
            let w__206 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__206 <b 549) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__207 : Bool)
      then
        (do
          writeReg SEE 549
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let size := (BitVec.slice __opcode 10 2)
          let S := (BitVec.slice __opcode 12 1)
          let opcode := (BitVec.slice __opcode 13 3)
          let R := (BitVec.slice __opcode 21 1)
          let L := (BitVec.slice __opcode 22 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_ldap1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered Rt Rn size S
            opcode R L Q)
          (pure false))
      else
        (do
          let w__209 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                     __opcode 29 10)) == (0x34061#20 : (BitVec 20)))) : Bool) : Bool)
            then
              (do
                let w__208 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__208 <b 550) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__209 : Bool)
          then
            (do
              writeReg SEE 550
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let size := (BitVec.slice __opcode 10 2)
              let S := (BitVec.slice __opcode 12 1)
              let opcode := (BitVec.slice __opcode 13 3)
              let R := (BitVec.slice __opcode 21 1)
              let L := (BitVec.slice __opcode 22 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_stl1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered Rt Rn size
                S opcode R L Q)
              (pure false))
          else
            (do
              let w__211 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                         __opcode 29 10)) == (0xE2FF0#20 : (BitVec 20)))) : Bool) : Bool)
                then
                  (do
                    let w__210 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__210 <b 551) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__211 : Bool)
              then
                (do
                  writeReg SEE 551
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rs := (BitVec.slice __opcode 16 5)
                  let size := (BitVec.slice __opcode 30 2)
                  if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 20)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size))
                  (pure false))
              else
                (do
                  let w__213 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                             __opcode 29 10)) == (0x67002#20 : (BitVec 20)))) : Bool) : Bool)
                    then
                      (do
                        let w__212 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__212 <b 552) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__213 : Bool)
                  then
                    (do
                      writeReg SEE 552
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let size := (BitVec.slice __opcode 30 2)
                      (decode_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback Rt Rn size)
                      (pure false))
                  else
                    (do
                      let w__215 ← (( do
                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31
                               10)) == (0b0011100010111111110000#22 : (BitVec 22))) : Bool) : Bool)
                        then
                          (do
                            let w__214 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__214 <b 553) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__215 : Bool)
                      then
                        (do
                          writeReg SEE 553
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Rs := (BitVec.slice __opcode 16 5)
                          let size := (BitVec.slice __opcode 30 2)
                          if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 20)])) != 1#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size))
                          (pure false))
                      else
                        (do
                          let w__217 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode
                                   31 10)) == (0b0111100010111111110000#22 : (BitVec 22))) : Bool) : Bool)
                            then
                              (do
                                let w__216 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__216 <b 554) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__217 : Bool)
                          then
                            (do
                              writeReg SEE 554
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Rs := (BitVec.slice __opcode 16 5)
                              let size := (BitVec.slice __opcode 30 2)
                              if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 20)])) != 1#1)) : Bool)
                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                              else
                                (do
                                  (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size))
                              (pure false))
                          else
                            (do
                              let w__219 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 29 21)) == (0b011001010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 11 10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__218 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__218 <b 555) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__219 : Bool)
                              then
                                (do
                                  writeReg SEE 555
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imm9 := (BitVec.slice __opcode 12 9)
                                  let opc := (BitVec.slice __opcode 22 2)
                                  let size := (BitVec.slice __opcode 30 2)
                                  (decode_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                    Rt Rn imm9 opc size)
                                  (pure false))
                              else
                                (do
                                  let w__221 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b00011001010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__220 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__220 <b 556) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__221 : Bool)
                                  then
                                    (do
                                      writeReg SEE 556
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imm9 := (BitVec.slice __opcode 12 9)
                                      let opc := (BitVec.slice __opcode 22 2)
                                      let size := (BitVec.slice __opcode 30 2)
                                      (decode_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                        Rt Rn imm9 opc size)
                                      (pure false))
                                  else
                                    (do
                                      let w__223 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b01011001010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__222 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__222 <b 557) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__223 : Bool)
                                      then
                                        (do
                                          writeReg SEE 557
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imm9 := (BitVec.slice __opcode 12 9)
                                          let opc := (BitVec.slice __opcode 22 2)
                                          let size := (BitVec.slice __opcode 30 2)
                                          (decode_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                            Rt Rn imm9 opc size)
                                          (pure false))
                                      else
                                        (do
                                          let w__225 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b000110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 11 10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__224 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__224 <b 558) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__225 : Bool)
                                          then
                                            (do
                                              writeReg SEE 558
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imm9 := (BitVec.slice __opcode 12 9)
                                              let opc := (BitVec.slice __opcode 22 2)
                                              let size := (BitVec.slice __opcode 30 2)
                                              (decode_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                Rt Rn imm9 opc size)
                                              (pure false))
                                          else
                                            (do
                                              let w__227 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 11 10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__226 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__226 <b 559) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__227 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 559
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imm9 := (BitVec.slice __opcode 12 9)
                                                  let opc := (BitVec.slice __opcode 22 2)
                                                  let size := (BitVec.slice __opcode 30 2)
                                                  (decode_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                    Rt Rn imm9 opc size)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__229 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b10011001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__228 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__228 <b 560) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__229 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 560
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imm9 := (BitVec.slice __opcode 12 9)
                                                      let opc := (BitVec.slice __opcode 22 2)
                                                      let size := (BitVec.slice __opcode 30 2)
                                                      (decode_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                        Rt Rn imm9 opc size)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__231 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                   __opcode 29 21)) == (0b011001000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 11 10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__230 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__230 <b 561) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__231 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 561
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imm9 := (BitVec.slice __opcode 12 9)
                                                          let opc := (BitVec.slice __opcode 22 2)
                                                          let size := (BitVec.slice __opcode 30 2)
                                                          (decode_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                            Rt Rn imm9 opc size)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__233 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b00011001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__232 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__232 <b 562) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__233 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 562
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imm9 :=
                                                                (BitVec.slice __opcode 12 9)
                                                              let opc :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let size :=
                                                                (BitVec.slice __opcode 30 2)
                                                              (decode_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                                Rt Rn imm9 opc size)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__235 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01011001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 11 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__234 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__234 <b 563) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__235 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 563
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let imm9 :=
                                                                    (BitVec.slice __opcode 12 9)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  (decode_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
                                                                    Rt Rn imm9 opc size)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__237 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 22 21)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__236 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__236 <b 564) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__237 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 564
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let imm9 :=
                                                                        (BitVec.slice __opcode 12 9)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      (decode_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered
                                                                        Rt Rn imm9 opc size)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__239 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 22 21)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__238 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__238 <b 565) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__239 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 565
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let imm9 :=
                                                                            (BitVec.slice __opcode
                                                                              12 9)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          (decode_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered
                                                                            Rt Rn imm9 opc size)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__241 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                     __opcode 29 10)) == (0x237FF#20 : (BitVec 20)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__240 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__240 <b 566) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__241 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 566
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rt2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 5)
                                                                              let o0 :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 20)])) != 1#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_ldar_aarch64_instrs_memory_ordered
                                                                                    Rt Rn Rt2 o0 Rs
                                                                                    L size))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__243 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                       __opcode 31
                                                                                       10)) == (0b0000100011011111111111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__242 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__242 <b 567) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__243 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 567
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rt2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 5)
                                                                                  let o0 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 15 1)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             20)])) != 1#1)) : Bool)
                                                                                  then
                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                      ()))
                                                                                  else
                                                                                    (do
                                                                                      (decode_ldarb_aarch64_instrs_memory_ordered
                                                                                        Rt Rn Rt2 o0
                                                                                        Rs L size))
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__245 ← (( do
                                                                                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           31 10)) == (0b0100100011011111111111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__244 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__244 <b 568) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__245 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 568
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Rt2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 5)
                                                                                      let o0 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          15 1)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let L :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 2)
                                                                                      if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 20)])) != 1#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_ldarh_aarch64_instrs_memory_ordered
                                                                                            Rt Rn
                                                                                            Rt2 o0
                                                                                            Rs L
                                                                                            size))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__247 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 29
                                                                                                 10)) == (0x237DF#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__246 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__246 <b 569) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__247 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 569
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Rt2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 5)
                                                                                          let o0 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              15 1)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let L :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     20)])) != 1#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_ldlar_aarch64_instrs_memory_ordered
                                                                                                Rt
                                                                                                Rn
                                                                                                Rt2
                                                                                                o0
                                                                                                Rs L
                                                                                                size))
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__249 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   10)) == (0b0000100011011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__248 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__248 <b 570) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__249 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 570
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
                                                                                              let Rt2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  5)
                                                                                              let o0 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  15
                                                                                                  1)
                                                                                              let Rs :=
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
                                                                                              if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         20)])) != 1#1)) : Bool)
                                                                                              then
                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                  ()))
                                                                                              else
                                                                                                (do
                                                                                                  (decode_ldlarb_aarch64_instrs_memory_ordered
                                                                                                    Rt
                                                                                                    Rn
                                                                                                    Rt2
                                                                                                    o0
                                                                                                    Rs
                                                                                                    L
                                                                                                    size))
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__251 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       31
                                                                                                       10)) == (0b0100100011011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__250 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__250 <b 571) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__251 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 571
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
                                                                                                  let Rt2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      5)
                                                                                                  let o0 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      15
                                                                                                      1)
                                                                                                  let Rs :=
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
                                                                                                  if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             20)])) != 1#1)) : Bool)
                                                                                                  then
                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                      ()))
                                                                                                  else
                                                                                                    (do
                                                                                                      (decode_ldlarh_aarch64_instrs_memory_ordered
                                                                                                        Rt
                                                                                                        Rn
                                                                                                        Rt2
                                                                                                        o0
                                                                                                        Rs
                                                                                                        L
                                                                                                        size))
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__253 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             29
                                                                                                             10)) == (0x227DF#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__252 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__252 <b 572) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__253 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 572
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
                                                                                                      let Rt2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          5)
                                                                                                      let o0 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          15
                                                                                                          1)
                                                                                                      let Rs :=
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
                                                                                                      if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 20)])) != 1#1)) : Bool)
                                                                                                      then
                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                          ()))
                                                                                                      else
                                                                                                        (do
                                                                                                          (decode_stllr_aarch64_instrs_memory_ordered
                                                                                                            Rt
                                                                                                            Rn
                                                                                                            Rt2
                                                                                                            o0
                                                                                                            Rs
                                                                                                            L
                                                                                                            size))
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__255 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               31
                                                                                                               10)) == (0b0000100010011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__254 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__254 <b 573) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__255 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 573
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
                                                                                                          let Rt2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              5)
                                                                                                          let o0 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              15
                                                                                                              1)
                                                                                                          let Rs :=
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
                                                                                                          if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     20)])) != 1#1)) : Bool)
                                                                                                          then
                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                              ()))
                                                                                                          else
                                                                                                            (do
                                                                                                              (decode_stllrb_aarch64_instrs_memory_ordered
                                                                                                                Rt
                                                                                                                Rn
                                                                                                                Rt2
                                                                                                                o0
                                                                                                                Rs
                                                                                                                L
                                                                                                                size))
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__257 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   31
                                                                                                                   10)) == (0b0100100010011111011111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__256 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__256 <b 574) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__257 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 574
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
                                                                                                              let Rt2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  5)
                                                                                                              let o0 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  15
                                                                                                                  1)
                                                                                                              let Rs :=
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
                                                                                                              if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         20)])) != 1#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_stllrh_aarch64_instrs_memory_ordered
                                                                                                                    Rt
                                                                                                                    Rn
                                                                                                                    Rt2
                                                                                                                    o0
                                                                                                                    Rs
                                                                                                                    L
                                                                                                                    size))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__259 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         29
                                                                                                                         10)) == (0x227FF#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__258 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__258 <b 575) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__259 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 575
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
                                                                                                                  let Rt2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      5)
                                                                                                                  let o0 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      15
                                                                                                                      1)
                                                                                                                  let Rs :=
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
                                                                                                                  if ((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                             __opcode
                                                                                                                                             11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                           __opcode
                                                                                                                                           12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     16)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             20)])) != 1#1)) : Bool)
                                                                                                                  then
                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                      ()))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      (decode_stlr_aarch64_instrs_memory_ordered
                                                                                                                        Rt
                                                                                                                        Rn
                                                                                                                        Rt2
                                                                                                                        o0
                                                                                                                        Rs
                                                                                                                        L
                                                                                                                        size))
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (pure true))))))))))))))))))))))))))))


end ArmFull.Functions
