import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0161
import ArmFull.Fn.M0162
import ArmFull.Fn.M0163
import ArmFull.Fn.M0164
import ArmFull.Fn.M0433
import ArmFull.Fn.M0434
import ArmFull.Fn.M0435
import ArmFull.Fn.M0437
import ArmFull.Fn.M0438
import ArmFull.Fn.M0439
import ArmFull.Fn.M0451
import ArmFull.Fn.M0466
import ArmFull.Fn.M0467
import ArmFull.Fn.M0468
import ArmFull.Fn.M0469
import ArmFull.Fn.M0470
import ArmFull.Fn.M0471
import ArmFull.Fn.M0472
import ArmFull.Fn.M0474
import ArmFull.Fn.M0475
import ArmFull.Fn.M0476
import ArmFull.Fn.M0501
import ArmFull.Fn.M0502
import ArmFull.Fn.M0503
import ArmFull.Fn.M0506
import ArmFull.Fn.M0507
import ArmFull.Fn.M0508
import ArmFull.Fn.M0509
import ArmFull.Fn.M0510
import ArmFull.Fn.M0511
import ArmFull.Fn.M0512
import ArmFull.Fn.M0513
import ArmFull.Fn.M0536
import ArmFull.Fn.M0538
import ArmFull.Fn.M0539
import ArmFull.Fn.M0540
import ArmFull.Fn.M1379
import ArmFull.Fn.M1385
import ArmFull.Fn.M1386
import ArmFull.Fn.M1388
import ArmFull.Fn.M1389
import ArmFull.Fn.M1390
import ArmFull.Fn.M1395
import ArmFull.Fn.M1400
import ArmFull.Fn.M1401
import ArmFull.Fn.M1402
import ArmFull.Fn.M1404

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

/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysRegWrite__seg4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Bool := do
  if ((((((CRm == 0b0000#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
  then
    (do
      (DACR32_EL2_SysRegWrite_94b89018206732e0 el op0 op1 CRn op2 CRm t)
      (pure false))
  else
    (do
      if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
      then
        (do
          (MAIR_EL2_SysRegWrite_c3f5f844df66ccc8 el op0 op1 CRn op2 CRm t)
          (pure false))
      else
        (do
          if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
          then
            (do
              (LORC_EL1_SysRegWrite_266317162c3d113d el op0 op1 CRn op2 CRm t)
              (pure false))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b111#3)) : Bool)
              then
                (do
                  (SCXTNUM_EL1_SysRegWrite_2b6dcbac83d50af9 el op0 op1 CRn op2 CRm t)
                  (pure false))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                  then
                    (do
                      (TCR_EL2_SysRegWrite_6c45c215eb6ac9ec el op0 op1 CRn op2 CRm t)
                      (pure false))
                  else
                    (do
                      if ((((((CRm == 0b1011#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                      then
                        (do
                          (ICC_ASGI1R_EL1_SysRegWrite_588d10b57224783c el op0 op1 CRn op2 CRm t)
                          (pure false))
                      else
                        (do
                          if ((((((CRm == 0b0011#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                          then
                            (do
                              (SPSR_und_SysRegWrite_684160009ec60b5e el op0 op1 CRn op2 CRm t)
                              (pure false))
                          else
                            (do
                              if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                              then
                                (do
                                  (SSBS_SysRegWrite_9913e9eaee3498e8 el op0 op1 CRn op2 CRm t)
                                  (pure false))
                              else
                                (do
                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b010#3)) : Bool)
                                  then
                                    (do
                                      (CPTR_EL3_SysRegWrite_3835d83d048c2034 el op0 op1 CRn op2 CRm
                                        t)
                                      (pure false))
                                  else
                                    (do
                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                      then
                                        (do
                                          (S2POR_EL1_SysRegWrite_9557ee7f2cc1821f el op0 op1 CRn op2
                                            CRm t)
                                          (pure false))
                                      else
                                        (do
                                          if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                          then
                                            (do
                                              (HFGRTR2_EL2_SysRegWrite_31d517272a11cc63 el op0 op1
                                                CRn op2 CRm t)
                                              (pure false))
                                          else
                                            (do
                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                              then
                                                (do
                                                  (TPIDRRO_EL0_SysRegWrite_7203698352c87d5e el op0
                                                    op1 CRn op2 CRm t)
                                                  (pure false))
                                              else
                                                (do
                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b010#3)) : Bool)
                                                  then
                                                    (do
                                                      (CNTP_CVAL_EL0_SysRegWrite_226b60eb1c89b722 el
                                                        op0 op1 CRn op2 CRm t)
                                                      (pure false))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b010#3)) : Bool)
                                                      then
                                                        (do
                                                          (RMR_EL3_SysRegWrite_d2303115883d7964 el
                                                            op0 op1 CRn op2 CRm t)
                                                          (pure false))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                          then
                                                            (do
                                                              (ICH_HCR_EL2_SysRegWrite_d09a9dfdfbf35716
                                                                el op0 op1 CRn op2 CRm t)
                                                              (pure false))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                              then
                                                                (do
                                                                  (ICC_IGRPEN0_EL1_SysRegWrite_dcea5bb07e468846
                                                                    el op0 op1 CRn op2 CRm t)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                  then
                                                                    (do
                                                                      (CNTHPS_TVAL_EL2_SysRegWrite_f57d636a80644cd9
                                                                        el op0 op1 CRn op2 CRm t)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                      then
                                                                        (do
                                                                          (MECID_A1_EL2_SysRegWrite_bc98456a1287bbce
                                                                            el op0 op1 CRn op2 CRm t)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                          then
                                                                            (do
                                                                              (AMAIR_EL1_SysRegWrite_88ac7594e16a57fe
                                                                                el op0 op1 CRn op2
                                                                                CRm t)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (SCXTNUM_EL0_SysRegWrite_9142402a828d0db8
                                                                                    el op0 op1 CRn
                                                                                    op2 CRm t)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (TPIDR2_EL0_SysRegWrite_6f661a4b0c2ce1c0
                                                                                        el op0 op1
                                                                                        CRn op2 CRm
                                                                                        t)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (PMCR_EL0_SysRegWrite_2f94c2f617db2cff
                                                                                            el op0
                                                                                            op1 CRn
                                                                                            op2 CRm
                                                                                            t)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (SPMEVCNTR_EL0_SysRegWrite_8ab800439a780c49
                                                                                                el
                                                                                                op0
                                                                                                op1
                                                                                                CRn
                                                                                                op2
                                                                                                CRm
                                                                                                t)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (SPMEVCNTR_EL0_SysRegWrite_be305c61a9d21074
                                                                                                    el
                                                                                                    op0
                                                                                                    op1
                                                                                                    CRn
                                                                                                    op2
                                                                                                    CRm
                                                                                                    t)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (SPMEVCNTR_EL0_SysRegWrite_e5c1db8ac0393d51
                                                                                                        el
                                                                                                        op0
                                                                                                        op1
                                                                                                        CRn
                                                                                                        op2
                                                                                                        CRm
                                                                                                        t)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (SPMEVCNTR_EL0_SysRegWrite_73acab900a26c809
                                                                                                            el
                                                                                                            op0
                                                                                                            op1
                                                                                                            CRn
                                                                                                            op2
                                                                                                            CRm
                                                                                                            t)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (SPMEVCNTR_EL0_SysRegWrite_08629c5414f88eb2
                                                                                                                el
                                                                                                                op0
                                                                                                                op1
                                                                                                                CRn
                                                                                                                op2
                                                                                                                CRm
                                                                                                                t)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (SPMEVCNTR_EL0_SysRegWrite_9c9ce3a923ecf708
                                                                                                                    el
                                                                                                                    op0
                                                                                                                    op1
                                                                                                                    CRn
                                                                                                                    op2
                                                                                                                    CRm
                                                                                                                    t)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (SPMEVCNTR_EL0_SysRegWrite_27dc77fd10e2aefe
                                                                                                                        el
                                                                                                                        op0
                                                                                                                        op1
                                                                                                                        CRn
                                                                                                                        op2
                                                                                                                        CRm
                                                                                                                        t)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (SPMEVCNTR_EL0_SysRegWrite_b2918213479c6eeb
                                                                                                                            el
                                                                                                                            op0
                                                                                                                            op1
                                                                                                                            CRn
                                                                                                                            op2
                                                                                                                            CRm
                                                                                                                            t)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (SPMEVCNTR_EL0_SysRegWrite_824f3bcfe3c44081
                                                                                                                                el
                                                                                                                                op0
                                                                                                                                op1
                                                                                                                                CRn
                                                                                                                                op2
                                                                                                                                CRm
                                                                                                                                t)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (SPMEVCNTR_EL0_SysRegWrite_10b130ab758fd16f
                                                                                                                                    el
                                                                                                                                    op0
                                                                                                                                    op1
                                                                                                                                    CRn
                                                                                                                                    op2
                                                                                                                                    CRm
                                                                                                                                    t)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (SPMEVCNTR_EL0_SysRegWrite_5ea3d20a15000ec4
                                                                                                                                        el
                                                                                                                                        op0
                                                                                                                                        op1
                                                                                                                                        CRn
                                                                                                                                        op2
                                                                                                                                        CRm
                                                                                                                                        t)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (SPMEVCNTR_EL0_SysRegWrite_07ced952b9f9c26f
                                                                                                                                            el
                                                                                                                                            op0
                                                                                                                                            op1
                                                                                                                                            CRn
                                                                                                                                            op2
                                                                                                                                            CRm
                                                                                                                                            t)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (SPMEVCNTR_EL0_SysRegWrite_00cca0c3f5f0c589
                                                                                                                                                el
                                                                                                                                                op0
                                                                                                                                                op1
                                                                                                                                                CRn
                                                                                                                                                op2
                                                                                                                                                CRm
                                                                                                                                                t)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (SPMEVCNTR_EL0_SysRegWrite_3653857cd3f8b570
                                                                                                                                                    el
                                                                                                                                                    op0
                                                                                                                                                    op1
                                                                                                                                                    CRn
                                                                                                                                                    op2
                                                                                                                                                    CRm
                                                                                                                                                    t)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (SPMEVCNTR_EL0_SysRegWrite_4e419851d7f8c37f
                                                                                                                                                        el
                                                                                                                                                        op0
                                                                                                                                                        op1
                                                                                                                                                        CRn
                                                                                                                                                        op2
                                                                                                                                                        CRm
                                                                                                                                                        t)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (SPMEVCNTR_EL0_SysRegWrite_2ea680a33713cf5f
                                                                                                                                                            el
                                                                                                                                                            op0
                                                                                                                                                            op1
                                                                                                                                                            CRn
                                                                                                                                                            op2
                                                                                                                                                            CRm
                                                                                                                                                            t)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (HDFGRTR2_EL2_SysRegWrite_43901f5d0ed8f1ff
                                                                                                                                                                el
                                                                                                                                                                op0
                                                                                                                                                                op1
                                                                                                                                                                CRn
                                                                                                                                                                op2
                                                                                                                                                                CRm
                                                                                                                                                                t)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b0001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (DBGPRCR_EL1_SysRegWrite_61b4445159bc717f
                                                                                                                                                                    el
                                                                                                                                                                    op0
                                                                                                                                                                    op1
                                                                                                                                                                    CRn
                                                                                                                                                                    op2
                                                                                                                                                                    CRm
                                                                                                                                                                    t)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (PMCNTENCLR_EL0_SysRegWrite_a090684957c3346b
                                                                                                                                                                        el
                                                                                                                                                                        op0
                                                                                                                                                                        op1
                                                                                                                                                                        CRn
                                                                                                                                                                        op2
                                                                                                                                                                        CRm
                                                                                                                                                                        t)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (SDER32_EL3_SysRegWrite_b1dc0570bf04f2cb
                                                                                                                                                                            el
                                                                                                                                                                            op0
                                                                                                                                                                            op1
                                                                                                                                                                            CRn
                                                                                                                                                                            op2
                                                                                                                                                                            CRm
                                                                                                                                                                            t)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (HPFAR_EL2_SysRegWrite_cc86ce0a0fcde19a
                                                                                                                                                                                el
                                                                                                                                                                                op0
                                                                                                                                                                                op1
                                                                                                                                                                                CRn
                                                                                                                                                                                op2
                                                                                                                                                                                CRm
                                                                                                                                                                                t)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (VMPIDR_EL2_SysRegWrite_652dff4d193b16d2
                                                                                                                                                                                    el
                                                                                                                                                                                    op0
                                                                                                                                                                                    op1
                                                                                                                                                                                    CRn
                                                                                                                                                                                    op2
                                                                                                                                                                                    CRm
                                                                                                                                                                                    t)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (MDSELR_EL1_SysRegWrite_96ef452973a846b6
                                                                                                                                                                                        el
                                                                                                                                                                                        op0
                                                                                                                                                                                        op1
                                                                                                                                                                                        CRn
                                                                                                                                                                                        op2
                                                                                                                                                                                        CRm
                                                                                                                                                                                        t)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (DBGDTR_EL0_SysRegWrite_a660c15660434176
                                                                                                                                                                                            el
                                                                                                                                                                                            op0
                                                                                                                                                                                            op1
                                                                                                                                                                                            CRn
                                                                                                                                                                                            op2
                                                                                                                                                                                            CRm
                                                                                                                                                                                            t)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              (ICV_EOIR0_EL1_SysRegWrite_4d99677932f49dc7
                                                                                                                                                                                                el
                                                                                                                                                                                                op0
                                                                                                                                                                                                op1
                                                                                                                                                                                                CRn
                                                                                                                                                                                                op2
                                                                                                                                                                                                CRm
                                                                                                                                                                                                t)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (APIAKeyHi_EL1_SysRegWrite_dd50986e83c65aba
                                                                                                                                                                                                    el
                                                                                                                                                                                                    op0
                                                                                                                                                                                                    op1
                                                                                                                                                                                                    CRn
                                                                                                                                                                                                    op2
                                                                                                                                                                                                    CRm
                                                                                                                                                                                                    t)
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (SCXTNUM_EL3_SysRegWrite_5070eac7134cb9ba
                                                                                                                                                                                                        el
                                                                                                                                                                                                        op0
                                                                                                                                                                                                        op1
                                                                                                                                                                                                        CRn
                                                                                                                                                                                                        op2
                                                                                                                                                                                                        CRm
                                                                                                                                                                                                        t)
                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          (APGAKeyHi_EL1_SysRegWrite_5d36b28ead1bb298
                                                                                                                                                                                                            el
                                                                                                                                                                                                            op0
                                                                                                                                                                                                            op1
                                                                                                                                                                                                            CRn
                                                                                                                                                                                                            op2
                                                                                                                                                                                                            CRm
                                                                                                                                                                                                            t)
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              (VBAR_EL3_SysRegWrite_a4ea3bd6f4a6393d
                                                                                                                                                                                                                el
                                                                                                                                                                                                                op0
                                                                                                                                                                                                                op1
                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                op2
                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                t)
                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  (TPIDR_EL0_SysRegWrite_0cc7097850c46a2a
                                                                                                                                                                                                                    el
                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (MDCR_EL2_SysRegWrite_b68bb751a2e2a82d
                                                                                                                                                                                                                        el
                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (SP_EL1_SysRegWrite_ef3afaab001d7071
                                                                                                                                                                                                                            el
                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (UAO_SysRegWrite_3265e241e210a049
                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (PIR_EL1_SysRegWrite_1431f0a180293b57
                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (PIR_EL1_SysRegWrite_da3aa8710c2ede05
                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (CNTKCTL_EL1_SysRegWrite_b6b89671d5078ba5
                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (PIR_EL2_SysRegWrite_7db7df9a9032c95e
                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (APIBKeyLo_EL1_SysRegWrite_7cc3f2a575353b80
                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (LORN_EL1_SysRegWrite_8a9df4ed50885fe4
                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (SPSR_EL3_SysRegWrite_456470f5b76b34d3
                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (APDBKeyHi_EL1_SysRegWrite_dcaaae97706e7922
                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (VMECID_P_EL2_SysRegWrite_b0549714107a13fc
                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      (SMPRIMAP_EL2_SysRegWrite_910f2a82defe4998
                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          (OSECCR_EL1_SysRegWrite_e6c17a3df51100b5
                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (DBGVCR32_EL2_SysRegWrite_2027ba18d0bb0f7c
                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (HFGRTR_EL2_SysRegWrite_fa73b98f16c9efee
                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (CPTR_EL2_SysRegWrite_26c85eb30bcb8d19
                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (CNTV_CVAL_EL0_SysRegWrite_ad2fa653919bf7cc
                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (HCRX_EL2_SysRegWrite_e32bbb7de8dc8ae3
                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (POR_EL0_SysRegWrite_ebaa371431c9b104
                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (SP_EL0_SysRegWrite_eb3954d261630177
                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (PMXEVCNTR_EL0_SysRegWrite_d3c59aa061d63534
                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (HFGWTR2_EL2_SysRegWrite_9115a08ec76ef20a
                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (SPMINTENSET_EL1_SysRegWrite_9368dd5ceffac1da
                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (PIRE0_EL2_SysRegWrite_13593dc3e37a5186
                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          (PIRE0_EL2_SysRegWrite_8aee2c676081a490
                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1000#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              (MECID_P1_EL2_SysRegWrite_3807276157365bf3
                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  (ICC_SGI1R_EL1_SysRegWrite_bd688469b6075cd1
                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      (HACR_EL2_SysRegWrite_a6347b2f3c503b39
                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          (SPMSELR_EL0_SysRegWrite_3811b80bc21b4614
                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              (AMAIR2_EL3_SysRegWrite_2519753087e4450a
                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  (DIT_SysRegWrite_cb82290c1722296d
                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      (SCR_EL3_SysRegWrite_b664c319973b52d6
                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (ICC_SRE_EL3_SysRegWrite_b650b212ede313fc
                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              (AFSR1_EL3_SysRegWrite_9124b1facd539906
                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  (HDFGWTR_EL2_SysRegWrite_5484cb7bd2cd2662
                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      (APGAKeyLo_EL1_SysRegWrite_8f5946d931efbfec
                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          (APDAKeyHi_EL1_SysRegWrite_9127291587c7ea6e
                                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b111#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              (CNTPS_CVAL_EL1_SysRegWrite_0efe14958ca47dee
                                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b111#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  (CNTPS_TVAL_EL1_SysRegWrite_fed363b581c49e0d
                                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      (MAIR2_EL3_SysRegWrite_47b59b09cadb288b
                                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
