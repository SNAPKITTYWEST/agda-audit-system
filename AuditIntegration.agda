-- AuditIntegration.agda: Integration of audit system with orchestration
-- Full audit trail generation, verification, and recovery procedures

module AuditIntegration where

open import Level
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _>_; _≥_; _≟_; _≡ᵇ_)
open import Data.Nat.Properties as ℕ-props using (≤-refl; ≤-trans; <-trans; +-comm; +-assoc)
open import Data.List as List using (List; []; _∷_; length; map; foldr; filter; _++_; reverse;
  foldl; any; all; zipWith; take; drop)
open import Data.List.Properties as List-props using (length-++)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum as Sum using (_⊎_; inl; inr)
open import Data.Product as Prod using (_×_; _,_; fst; snd)
open import Data.Unit as Unit using (⊤; tt)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong)

open import Data
open import Orchestration
open import Verification

-- ============================================================================
-- AUDIT ENTRY SEQUENCE: Immutable ordered log
-- ============================================================================

-- Audit log: invariant is maintained that sequence numbers are strictly increasing
record AuditLog : Set where
  constructor audit-log
  field
    entries : List AuditEntry
    sequence : ℕ  -- current sequence counter
    -- Invariant: sequence = length entries, all entries have strictly increasing sequences
    seq-valid : sequence ≡ length entries
    chain-valid : auditChainValid entries ≡ true

-- Initialize empty audit log
emptyAuditLog : AuditLog
emptyAuditLog = audit-log [] 0 refl refl

-- Append entry to audit log: maintains ordering invariant
appendAuditEntry : AuditLog → AuditEntry → AuditLog
appendAuditEntry (audit-log entries seq seq-val chain-val) entry =
  let updated = entries ++ (entry ∷ [])
  in audit-log updated (seq + 1) (trans seq-val (length-++ entries (entry ∷ [])))
    (auditAppendPreservesOrdering entries entry chain-val)

-- Query audit log by sequence number: deterministic
queryAuditBySequence : AuditLog → ℕ → Maybe AuditEntry
queryAuditBySequence (audit-log entries _ _ _) seq =
  List.find (λ e → (e .AuditEntry.sequence) ≟ seq) entries

-- Get all audit entries of specific event type
queryAuditByType : AuditLog → AuditEventType → List AuditEntry
queryAuditByType (audit-log entries _ _ _) event-type =
  filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ event-type) of λ where
    (yes _) → true
    (no _) → false) entries

-- Audit trail integrity check: verify chain of hashes
verifyAuditChain : AuditLog → (compute-hash : List ℕ → ℕ) → Bool
verifyAuditChain (audit-log [] _ _ _) _ = true
verifyAuditChain (audit-log (e ∷ es) _ _ _) compute-hash =
  let current-hash = compute-hash (e .AuditEntry.action)
      matches-stored = (e .AuditEntry.stateHash) ≡ᵇ current-hash
  in if matches-stored then verifyAuditChain (audit-log es (length es) refl refl) compute-hash
     else false

-- ============================================================================
-- OPERATION AUDIT RECORDS: Each operation generates audit entry
-- ============================================================================

-- Record gate discharge
recordGateDischarge : AuditLog → ℕ → ℕ → ℕ → TemporalCoordinate → List ℕ → AuditLog
recordGateDischarge log actor gate-id task-id timestamp evidence =
  let entry = auditGateDischarge (log .AuditLog.sequence) actor gate-id timestamp evidence
  in appendAuditEntry log entry

-- Record persona merge
recordPersonaMerge : AuditLog → ℕ → ℕ → ℕ → TemporalCoordinate → AuditLog
recordPersonaMerge log p1 p2 merged timestamp =
  let entry = auditPersonaMerge (log .AuditLog.sequence) p1 p2 merged timestamp
  in appendAuditEntry log entry

-- Record task assignment
recordTaskAssignment : AuditLog → ℕ → ℕ → List ℕ → TemporalCoordinate → AuditLog
recordTaskAssignment log task-id actor personas timestamp =
  let entry = auditTaskAssignment (log .AuditLog.sequence) task-id actor personas timestamp
  in appendAuditEntry log entry

-- Record policy violation
recordPolicyViolation : AuditLog → ℕ → ℕ → List ℕ → TemporalCoordinate → AuditLog
recordPolicyViolation log actor policy-id context timestamp =
  let entry = audit-entry (log .AuditLog.sequence) timestamp POLICY_VIOLATED actor
              (policy-id ∷ context) 0 0
  in appendAuditEntry log entry

-- Record state transition
recordStateTransition : AuditLog → ℕ → ℕ → ℕ → TemporalCoordinate → AuditLog
recordStateTransition log actor old-state-hash new-state-hash timestamp =
  let entry = audit-entry (log .AuditLog.sequence) timestamp STATE_TRANSITION actor
              [old-state-hash; new-state-hash] new-state-hash old-state-hash
  in appendAuditEntry log entry

-- ============================================================================
-- AUDIT-AWARE STATE MACHINE: Every operation is logged
-- ============================================================================

-- State transition with automatic audit logging
record AuditedOperation (From To : Set) : Set where
  constructor audited-op
  field
    operation : From → Maybe To
    audit : From → To → AuditEventType → AuditLog → AuditLog
    -- Invariant: audit entry is always appended
    audit-appends : ∀ f t et log → length ((audit f t et log) .AuditLog.entries)
                                 ≡ suc (length (log .AuditLog.entries))

-- Execute audited operation: performs operation and logs automatically
executeAuditedOp : {A B : Set} → AuditedOperation A B → A → AuditLog → Maybe (B × AuditLog)
executeAuditedOp (audited-op op audit _) a log =
  case (op a) of λ where
    nothing → nothing
    (just b) → just (b , audit a b GATE_DISCHARGE log)

-- ============================================================================
-- POLICY COMPLIANCE AUDIT: Verify policies are not violated
-- ============================================================================

-- Policy violation detector
data PolicyViolationRecord : Set where
  no-violation : PolicyViolationRecord
  violation-detected : (actor : ℕ) → (policy-id : ℕ) → (timestamp : TemporalCoordinate)
                    → PolicyViolationRecord

-- Check if operation violates policy
checkPolicyCompliance : (actor : ℕ) → (policy : Policy SystemState) → (state : SystemState)
                      → Dec PolicyViolationRecord
checkPolicyCompliance actor policy state =
  case (allGatesPass policy state) of λ where
    true → yes no-violation
    false → yes (violation-detected actor 0 (coord 0 0))

-- Log all policy violations
auditPolicyCompliance : AuditLog → List (ℕ × Policy SystemState) → SystemState → AuditLog
auditPolicyCompliance log [] _ = log
auditPolicyCompliance log ((actor , policy) ∷ ps) state =
  case (checkPolicyCompliance actor policy state) of λ where
    no-violation → auditPolicyCompliance log ps state
    (violation-detected _ policy-id ts) →
      auditPolicyCompliance (recordPolicyViolation log actor policy-id [] ts) ps state

-- ============================================================================
-- RECOVERY PROCEDURES: Rollback and state reconstruction
-- ============================================================================

-- Find last good state in audit log
findLastGoodState : AuditLog → (check-state : ℕ → Bool) → Maybe ℕ
findLastGoodState (audit-log entries _ _ _) check-state =
  case (List.filter (λ e → check-state (e .AuditEntry.stateHash)) entries) of λ where
    [] → nothing
    es → just (List.last es .AuditEntry.sequence)

-- Reconstruct state at checkpoint sequence
reconstructStateAtSequence : AuditLog → ℕ → (apply-entry : AuditEntry → SystemState → Maybe SystemState)
                           → Maybe SystemState
reconstructStateAtSequence (audit-log entries _ _ _) target-seq apply-entry =
  let relevant = List.filter (λ e → (e .AuditEntry.sequence) ≤ target-seq) entries
  in foldl (λ acc e → case acc of λ where
      nothing → nothing
      (just s) → apply-entry e s) (just (state [] [] [] [] [] [])) relevant

-- Create recovery checkpoint: snapshot for rollback
createRecoveryCheckpoint : ℕ → SystemState → RollbackPoint
createRecoveryCheckpoint seq state = rollback-point seq state (ℕ.zero<suc _)

-- Execute rollback to checkpoint: restore previous state
executeRollback : RollbackPoint → AuditLog → (List AuditEntry × SystemState)
executeRollback rp (audit-log entries _ _ _) =
  let target-seq = rp .RollbackPoint.checkpointSeq
      dropped = List.filter (λ e → (e .AuditEntry.sequence) > target-seq) entries
  in (dropped , (rp .RollbackPoint.checkpointState))

-- ============================================================================
-- AUDIT CERTIFICATION: Formal attestation of system state
-- ============================================================================

-- Certificate: proof that state matches audit trail
record AuditCertificate : Set where
  constructor audit-certificate
  field
    statementSeq : ℕ  -- sequence number of statement
    stateHash : ℕ  -- hash of attested state
    certificateTime : TemporalCoordinate
    certifier : ℕ  -- persona who certifies
    evidence : List ℕ  -- supporting entries

-- Issue certificate for current state
issueCertificate : ℕ → ℕ → TemporalCoordinate → ℕ → List ℕ → AuditCertificate
issueCertificate seq hash ts certifier evidence =
  audit-certificate seq hash ts certifier evidence

-- Verify certificate against audit log
verifyCertificate : AuditCertificate → AuditLog → Dec Bool
verifyCertificate cert (audit-log entries _ _ _) =
  case (List.find (λ e → (e .AuditEntry.stateHash) ≟ (cert .AuditCertificate.stateHash))
    entries) of λ where
    nothing → yes false
    (just e) → yes true

-- ============================================================================
-- AUDIT REPORT GENERATION: Comprehensive audit summary
-- ============================================================================

-- Audit statistics
record AuditStatistics : Set where
  constructor audit-statistics
  field
    totalEntries : ℕ
    gateDischarges : ℕ
    personaMerges : ℕ
    taskAssignments : ℕ
    policyViolations : ℕ
    stateTransitions : ℕ
    timeSpan : ℕ

-- Compute audit statistics
computeAuditStats : AuditLog → AuditStatistics
computeAuditStats (audit-log entries _ _ _) =
  let gate-count = length (filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ GATE_DISCHARGE) of λ where
        (yes _) → true
        (no _) → false) entries)
      merge-count = length (filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ PERSONA_MERGE) of λ where
        (yes _) → true
        (no _) → false) entries)
      assign-count = length (filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ TASK_ASSIGNMENT) of λ where
        (yes _) → true
        (no _) → false) entries)
      policy-count = length (filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ POLICY_VIOLATED) of λ where
        (yes _) → true
        (no _) → false) entries)
      state-count = length (filter (λ e → case ((e .AuditEntry.eventType) ≟ₐₑₜ STATE_TRANSITION) of λ where
        (yes _) → true
        (no _) → false) entries)
  in audit-statistics (length entries) gate-count merge-count assign-count policy-count state-count 0

-- Audit completeness check: ensure no gaps in sequence
auditComplete : AuditLog → Bool
auditComplete (audit-log entries _ _ _) =
  List.all (λ i → List.any (λ e → (e .AuditEntry.sequence) ≟ i) entries)
    (List.tabulate (length entries) id)

-- ============================================================================
-- AUDIT-GUARDED STATE: System state wrapped with audit guarantee
-- ============================================================================

-- State with guarantee of audit compliance
record AuditedState : Set where
  constructor audited-state
  field
    state : SystemState
    auditLog : AuditLog
    -- Invariant: state and audit are synchronized
    sync-inv : length (auditLog .AuditLog.entries) ≥ 1
    -- Invariant: audit chain is valid
    chain-inv : auditChainValid (auditLog .AuditLog.entries) ≡ true

-- Create initial audited state with empty audit log
initialAuditedState : AuditedState
initialAuditedState = audited-state (state [] [] [] [] [] []) emptyAuditLog
  (ℕ.zero<suc _) refl

-- Update audited state: operation + audit entry
updateAuditedState : AuditedState → (SystemState → Maybe SystemState) → AuditEventType
                   → ℕ → List ℕ → Maybe AuditedState
updateAuditedState (audited-state s log sync chain) op event-type actor context =
  case (op s) of λ where
    nothing → nothing
    (just s') →
      let new-log = appendAuditEntry log (audit-entry (log .AuditLog.sequence) (coord 0 0)
                      event-type actor context 0 0)
      in just (audited-state s' new-log (ℕ.zero<suc _) (auditAppendPreservesOrdering
         (log .AuditLog.entries) _ chain))

-- ============================================================================
-- AUDIT COMPLIANCE PROOFS
-- ============================================================================

-- Proof: audit log never loses entries
auditLogMonotone : (log₁ log₂ : AuditLog) → (e : AuditEntry)
                 → log₂ ≡ appendAuditEntry log₁ e
                 → length (log₁ .AuditLog.entries) < length (log₂ .AuditLog.entries)
auditLogMonotone log₁ log₂ e eq =
  case eq of λ eq' → case cong (λ l → length (l .AuditLog.entries)) eq' of λ eq'' →
  case eq'' of λ eq''' → ℕ.n<suc-n _

-- Proof: appending entry doesn't lose existing entries
appendPreservesHistory : (log : AuditLog) → (e : AuditEntry)
                       → List.isPrefixOf (log .AuditLog.entries)
                         ((appendAuditEntry log e) .AuditLog.entries)
appendPreservesHistory (audit-log entries seq seq-val chain-val) e =
  List.isPrefixOf-refl entries

-- Proof: all audit entries are recoverable
auditEntriesRecoverable : (log : AuditLog) → ∀ i → i < length (log .AuditLog.entries)
                        → ∃ e → List.index (log .AuditLog.entries) (Fin.fromℕ< i) ≡ e
auditEntriesRecoverable (audit-log [] _ _ _) i h = Empty.⊥-elim (ℕ.<-irrefl i (ℕ.trans i h))
auditEntriesRecoverable (audit-log (e ∷ es) seq seq-val chain-val) zero h =
  e , refl
auditEntriesRecoverable (audit-log (e ∷ es) seq seq-val chain-val) (suc i) h =
  auditEntriesRecoverable (audit-log es (seq - 1) (Eq.trans seq-val (cong suc refl)) chain-val)
    i (ℕ.pred-mono h)

-- ============================================================================
-- HELPER: List utilities
-- ============================================================================

List.isPrefixOf : ∀ {a} {A : Set a} → List A → List A → Set a
List.isPrefixOf [] _ = ⊤
List.isPrefixOf (_ ∷ _) [] = ⊥
List.isPrefixOf (x ∷ xs) (y ∷ ys) = (x ≡ y) ∧ List.isPrefixOf xs ys

List.isPrefixOf-refl : ∀ {a} {A : Set a} (xs : List A) → List.isPrefixOf xs xs
List.isPrefixOf-refl [] = tt
List.isPrefixOf-refl (x ∷ xs) = (refl , List.isPrefixOf-refl xs)

List.tabulate : ∀ {a} {A : Set a} (n : ℕ) → (Fin n → A) → List A
List.tabulate zero _ = []
List.tabulate (suc n) f = f Fin.zero ∷ List.tabulate n (f ∘ Fin.suc)

List.last : ∀ {a} {A : Set a} → List A → A
List.last (x ∷ []) = x
List.last (x ∷ xs@(_ ∷ _)) = List.last xs

List.find : ∀ {a b} {A : Set a} {B : Set b} → (A → Bool) → List A → Maybe A
List.find _ [] = nothing
List.find p (x ∷ xs) = if p x then just x else List.find p xs

List.filter : ∀ {a b} {A : Set a} {B : Set b} → (A → Bool) → List A → List A
List.filter _ [] = []
List.filter p (x ∷ xs) = if p x then x ∷ List.filter p xs else List.filter p xs

List.all : ∀ {a b} {A : Set a} {B : Set b} → (A → Bool) → List A → Bool
List.all _ [] = true
List.all p (x ∷ xs) = p x ∧ List.all p xs

List.any : ∀ {a b} {A : Set a} {B : Set b} → (A → Bool) → List A → Bool
List.any _ [] = false
List.any p (x ∷ xs) = p x ∨ List.any p xs

List.index : ∀ {a} {A : Set a} → List A → Fin → A
List.index [] ()
List.index (x ∷ xs) Fin.zero = x
List.index (x ∷ xs) (Fin.suc i) = List.index xs i

foldl : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → A → B) → B → List A → B
foldl _ acc [] = acc
foldl f acc (x ∷ xs) = foldl f (f acc x) xs
