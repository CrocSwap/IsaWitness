import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0142
import ArmFull.Fn.M0160
import ArmFull.Fn.M0213
import ArmFull.Fn.M0214
import ArmFull.Fn.M0313
import ArmFull.Fn.M0314
import ArmFull.Fn.M0315
import ArmFull.Fn.M0316
import ArmFull.Fn.M0327
import ArmFull.Fn.M0343
import ArmFull.Fn.M0344
import ArmFull.Fn.M0346
import ArmFull.Fn.M0349
import ArmFull.Fn.M0350
import ArmFull.Fn.M0356
import ArmFull.Fn.M0359
import ArmFull.Fn.M0360
import ArmFull.Fn.M0361
import ArmFull.Fn.M0362
import ArmFull.Fn.M0363
import ArmFull.Fn.M0364
import ArmFull.Fn.M0365
import ArmFull.Fn.M0366
import ArmFull.Fn.M0367
import ArmFull.Fn.M0368
import ArmFull.Fn.M0369
import ArmFull.Fn.M0387
import ArmFull.Fn.M0389
import ArmFull.Fn.M0390
import ArmFull.Fn.M0392
import ArmFull.Fn.M0395
import ArmFull.Fn.M0405
import ArmFull.Fn.M0406
import ArmFull.Fn.M0407
import ArmFull.Fn.M0408
import ArmFull.Fn.M0409
import ArmFull.Fn.M0410
import ArmFull.Fn.M0411
import ArmFull.Fn.M0412
import ArmFull.Fn.M0413
import ArmFull.Fn.M0428
import ArmFull.Fn.M0429
import ArmFull.Fn.M0430
import ArmFull.Fn.M0431
import ArmFull.Fn.M1351
import ArmFull.Fn.M1357
import ArmFull.Fn.M1358
import ArmFull.Fn.M1361
import ArmFull.Fn.M1362
import ArmFull.Fn.M1372
import ArmFull.Fn.M1374
import ArmFull.Fn.M1375
import ArmFull.Fn.M1377

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
def AArch64_AutoGen_SysRegRead__seg2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Bool := do
  if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
  then
    (do
      (PMCCFILTR_EL0_SysRegRead_5ac92cf4fcc5c832 el op0 op1 CRn op2 CRm t)
      (pure false))
  else
    (do
      if ((((((CRm == 0b1000#4) && (CRn == 0b0111#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
      then
        (do
          (DBGCLAIMSET_EL1_SysRegRead_e478959c32681458 el op0 op1 CRn op2 CRm t)
          (pure false))
      else
        (do
          if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (SPMCGCR_EL1_SysRegRead_529e10a6261e7d96 el op0 op1 CRn op2 CRm t)
              (pure false))
          else
            (do
              if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
              then
                (do
                  (SPMCGCR_EL1_SysRegRead_529e10a6261e7d96 el op0 op1 CRn op2 CRm t)
                  (pure false))
              else
                (do
                  if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                  then
                    (do
                      (ICC_SRE_EL1_SysRegRead_66e16dcbec736265 el op0 op1 CRn op2 CRm t)
                      (pure false))
                  else
                    (do
                      if ((((((CRm == 0b0011#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                      then
                        (do
                          (PM_SysRegRead_801ea1615b4051f7 el op0 op1 CRn op2 CRm t)
                          (pure false))
                      else
                        (do
                          if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                          then
                            (do
                              (ICH_AP0R_EL2_SysRegRead_52a53932b4c339f0 el op0 op1 CRn op2 CRm t)
                              (pure false))
                          else
                            (do
                              if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                              then
                                (do
                                  (ICH_AP0R_EL2_SysRegRead_e9c19cba17805bc5 el op0 op1 CRn op2 CRm t)
                                  (pure false))
                              else
                                (do
                                  if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                  then
                                    (do
                                      (ICH_AP0R_EL2_SysRegRead_59f0de8946000971 el op0 op1 CRn op2
                                        CRm t)
                                      (pure false))
                                  else
                                    (do
                                      if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                      then
                                        (do
                                          (ICH_AP0R_EL2_SysRegRead_5c5dde09d918dae7 el op0 op1 CRn
                                            op2 CRm t)
                                          (pure false))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                          then
                                            (do
                                              (CONTEXTIDR_EL1_SysRegRead_c6da578db1984530 el op0 op1
                                                CRn op2 CRm t)
                                              (pure false))
                                          else
                                            (do
                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                              then
                                                (do
                                                  (TPIDR_EL1_SysRegRead_cb207f415778832f el op0 op1
                                                    CRn op2 CRm t)
                                                  (pure false))
                                              else
                                                (do
                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                  then
                                                    (do
                                                      (ID_ISAR4_EL1_SysRegRead_b41d0fd5cce0f813 el
                                                        op0 op1 CRn op2 CRm t)
                                                      (pure false))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                      then
                                                        (do
                                                          (CNTVOFF_EL2_SysRegRead_f84a995c7f5f427c
                                                            el op0 op1 CRn op2 CRm t)
                                                          (pure false))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                          then
                                                            (do
                                                              (ID_ISAR1_EL1_SysRegRead_659998c6404a0adc
                                                                el op0 op1 CRn op2 CRm t)
                                                              (pure false))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                              then
                                                                (do
                                                                  (PMUACR_EL1_SysRegRead_ce94146f70da9e11
                                                                    el op0 op1 CRn op2 CRm t)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                  then
                                                                    (do
                                                                      (DSPSR_EL0_SysRegRead_e92e924519c42368
                                                                        el op0 op1 CRn op2 CRm t)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                      then
                                                                        (do
                                                                          (ACTLR_EL1_SysRegRead_cc5a0755f0205a72
                                                                            el op0 op1 CRn op2 CRm t)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                          then
                                                                            (do
                                                                              (RMR_EL2_SysRegRead_0cc9a425a7ab6f44
                                                                                el op0 op1 CRn op2
                                                                                CRm t)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (VNCR_EL2_SysRegRead_fd49e25478d53eb1
                                                                                    el op0 op1 CRn
                                                                                    op2 CRm t)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (PMINTENCLR_EL1_SysRegRead_fb98bdd5aa053775
                                                                                        el op0 op1
                                                                                        CRn op2 CRm
                                                                                        t)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (PMSELR_EL0_SysRegRead_597778422a5e1e61
                                                                                            el op0
                                                                                            op1 CRn
                                                                                            op2 CRm
                                                                                            t)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (ICC_CTLR_EL1_SysRegRead_eb1de12df33d5c37
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
                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (SPMEVFILT2R_EL0_SysRegRead_d0361acb26713433
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
                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (SPMEVFILT2R_EL0_SysRegRead_d72b4e2f828258be
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
                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (SPMEVFILT2R_EL0_SysRegRead_433638c7dd5d7f8c
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
                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (SPMEVFILT2R_EL0_SysRegRead_4309271c5c3f50c2
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
                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (SPMEVFILT2R_EL0_SysRegRead_a505a5c15b00753c
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
                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (SPMEVFILT2R_EL0_SysRegRead_51af2efaff004e74
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
                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (SPMEVFILT2R_EL0_SysRegRead_b92ce31d6b189d89
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
                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (SPMEVFILT2R_EL0_SysRegRead_811ad3f997f59858
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
                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (SPMEVFILT2R_EL0_SysRegRead_c26a621e717d6ec0
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
                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (SPMEVFILT2R_EL0_SysRegRead_becf2c3488c0840f
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
                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (SPMEVFILT2R_EL0_SysRegRead_310eb78ca3ffcdd5
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
                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (SPMEVFILT2R_EL0_SysRegRead_dc68673c986189cc
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
                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (SPMEVFILT2R_EL0_SysRegRead_0f60cc3cb4a8e9b3
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
                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (SPMEVFILT2R_EL0_SysRegRead_3c202af9a88305f9
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
                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (SPMEVFILT2R_EL0_SysRegRead_53e34bafcb1745bf
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
                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (SPMEVFILT2R_EL0_SysRegRead_5f57fc70d1c81668
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
                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (ID_ISAR6_EL1_SysRegRead_c5d967e39ea7cb96
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
                                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (ICC_AP1R_EL1_SysRegRead_6535748ba14d930e
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
                                                                                                                                                                      if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (ICC_AP1R_EL1_SysRegRead_5a702399a390f8ec
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
                                                                                                                                                                          if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (ICC_AP1R_EL1_SysRegRead_39371d4468952849
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
                                                                                                                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (ICC_AP1R_EL1_SysRegRead_a0d3f3e1a65fa7f7
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
                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (DAIF_SysRegRead_102c97f1f2780854
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
                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (CNTP_CTL_EL0_SysRegRead_15357e2547a6f65f
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
                                                                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_e5a283ed2b79bd84
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
                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_32b4fcb392e5c312
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
                                                                                                                                                                                                  if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_53822901bce95688
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
                                                                                                                                                                                                      if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_593e15d8d87f3370
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
                                                                                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_6eef6c9d0ea660a1
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
                                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_fccbe0710386c98a
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
                                                                                                                                                                                                                  if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_bddfd936634ddadc
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
                                                                                                                                                                                                                      if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_6d59e307d3cd7a1c
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
                                                                                                                                                                                                                          if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_748d6e2e7bd869de
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
                                                                                                                                                                                                                              if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_e23b48b5ac325a95
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
                                                                                                                                                                                                                                  if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_6b9b795fff65a19d
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
                                                                                                                                                                                                                                      if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_3fd74d86919a41a5
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
                                                                                                                                                                                                                                          if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_693e4ccc8252a9a7
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
                                                                                                                                                                                                                                              if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_ef3a8d2a7921c11c
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
                                                                                                                                                                                                                                                  if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_73ed225f0812fbfc
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
                                                                                                                                                                                                                                                      if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_0d3db5f733fce750
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
                                                                                                                                                                                                                                                          if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_c3ba32793ae88442
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
                                                                                                                                                                                                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_3cf749b2a6f0d8e8
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
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_1182d540f254acac
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
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_ca58b1e5989f1015
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
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_0593376102dfa06d
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
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_a360f253ceba1de0
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
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_10f19f05478e0298
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
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_2a52665b668ba6a3
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
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_1ab539f73d82d8d9
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
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_0fa6d9f54f3566c9
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
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_776dc50ca01e0285
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
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegRead_3152dcccddae7402
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
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegRead_2f26e246b6e98799
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
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegRead_81c5bd2bbc23b640
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
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegRead_ed4b4b8084b6d41d
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
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          (HFGITR2_EL2_SysRegRead_9589905774d1f5d8
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
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              (CNTHV_TVAL_EL2_SysRegRead_42829873ebd7042d
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
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  (CNTHV_TVAL_EL2_SysRegRead_131a29f8b5d31ce1
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
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      (SPSR_irq_SysRegRead_3f8614ad01700094
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
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          (SPMOVSSET_EL0_SysRegRead_5f97da0caf1e7976
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
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              (ICH_MISR_EL2_SysRegRead_c4aa5214cb9e1506
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
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  (CNTHP_CVAL_EL2_SysRegRead_5a841847b0720163
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
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      (CNTHP_CVAL_EL2_SysRegRead_ed1c928371f03392
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
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b010#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (CSSELR_EL1_SysRegRead_5913225fc951e4d2
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
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              (PFAR_EL2_SysRegRead_b491a80fcabf31ea
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
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0110#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  (MFAR_EL3_SysRegRead_6520d659502d749b
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
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      (SPSR_EL2_SysRegRead_f8dd5a5a3ce06a92
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
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          (SPSR_EL2_SysRegRead_c62428913c72a08e
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
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              (TCR_EL1_SysRegRead_906af64cf526e3f6
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
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  (TCR_EL1_SysRegRead_3c972cf7b788a8a1
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
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      (SCTLR2_EL1_SysRegRead_e0ec1b448b49d808
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
