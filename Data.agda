-- Data.agda: Formal data structures for orchestration and audit system
-- Pure formal definitions with invariants encoded at the type level

module Data where

open import Level
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _>_; _≥_; compare)
open import Data.Nat.Properties as ℕ-props using (≤-refl; ≤-trans; <-trans)
open import Data.List as List using (List; []; _∷_; length; map; foldr; filter; _++_)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum as Sum using (_⊎_; inl; inr)
open import Data.Product as Prod using (_×_; _,_; fst; snd; uncurry)
open import Data.Unit as Unit using (⊤; tt)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable as Dec using (map)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; subst)

-- ============================================================================
-- TEMPORAL COORDINATE SYSTEM: T = (notebook_k, page_j)
-- ============================================================================

record TemporalCoordinate : Set where
  constructor coord
  field
    notebook : ℕ
    page     : ℕ

-- Lexicographic order on temporal coordinates
_<ᵗ_ : TemporalCoordinate → TemporalCoordinate → Set
(coord k₁ j₁) <ᵗ (coord k₂ j₂) =
  (k₁ < k₂) ⊎ (k₁ ≡ k₂ ∧ j₁ < j₂)

-- Decision procedure for temporal ordering
_<ᵗ?_ : (t₁ t₂ : TemporalCoordinate) → Dec (t₁ <ᵗ t₂)
(coord k₁ j₁) <ᵗ? (coord k₂ j₂) with k₁ ℕ.<? k₂
... | yes h = yes (inl h)
... | no ¬h with k₁ ℕ.≟ k₂
... | yes eq with j₁ ℕ.<? j₂
... | yes h = yes (inr (eq , h))
... | no ¬h = no λ h → case h of λ where
    (inl h') → ¬h (ℕ.<-irrefl k₁ (Eq.trans h' (Eq.sym eq)))
    (inr (_ , j-lt)) → ¬h j-lt
... | no ¬eq = no λ h → case h of λ where
    (inl h') → ¬h h'
    (inr (eq , _)) → ¬eq eq

-- ============================================================================
-- NODE TYPES AND SYMBOLIC NODES
-- ============================================================================

data NodeType : Set where
  SYMBOL   : NodeType  -- recurring imaginal images
  FIGURE   : NodeType  -- named entities
  OBJECT   : NodeType  -- physical items
  PLACE    : NodeType  -- locations
  ACTION   : NodeType  -- events, processes
  COLOR    : NodeType  -- chromatic attributes
  NUMBER   : NodeType  -- numerical occurrences
  FORM     : NodeType  -- geometric shapes
  ANIMAL   : NodeType  -- zoomorphic entities
  ELEMENT  : NodeType  -- elemental forces
  TEXT     : NodeType  -- textual units
  DREAM    : NodeType  -- dream-mode events
  VISION   : NodeType  -- active imagination/vision-mode
  TEMPORAL : NodeType  -- temporal references

-- Decision equality on node types
_≟ₙₜ_ : (a b : NodeType) → Dec (a ≡ b)
SYMBOL ≟ₙₜ SYMBOL = yes refl
FIGURE ≟ₙₜ FIGURE = yes refl
OBJECT ≟ₙₜ OBJECT = yes refl
PLACE ≟ₙₜ PLACE = yes refl
ACTION ≟ₙₜ ACTION = yes refl
COLOR ≟ₙₜ COLOR = yes refl
NUMBER ≟ₙₜ NUMBER = yes refl
FORM ≟ₙₜ FORM = yes refl
ANIMAL ≟ₙₜ ANIMAL = yes refl
ELEMENT ≟ₙₜ ELEMENT = yes refl
TEXT ≟ₙₜ TEXT = yes refl
DREAM ≟ₙₜ DREAM = yes refl
VISION ≟ₙₜ VISION = yes refl
TEMPORAL ≟ₙₜ TEMPORAL = yes refl
_ ≟ₙₜ _ = no λ ()

-- Symbolic node identifier
NodeId : Set
NodeId = ℕ

-- Symbolic node with invariants
record SymbolicNode : Set where
  constructor node
  field
    id        : NodeId
    types     : List NodeType  -- nodes can have multiple type tags
    firstAppearance : TemporalCoordinate
    lastAppearance  : TemporalCoordinate
    isActive  : Bool
    -- INVARIANT: firstAppearance ≤ᵗ lastAppearance
    coord-inv : (firstAppearance <ᵗ lastAppearance) ⊎ (firstAppearance ≡ lastAppearance)

-- Span of a symbolic node (temporal persistence)
span : SymbolicNode → ℕ
span (node _ _ (coord k₁ j₁) (coord k₂ j₂) _ _) =
  if k₁ ≟ k₂ then (j₂ - j₁) else ((k₂ - k₁) * 100 + (j₂ - j₁))

-- ============================================================================
-- EDGE LABELS AND EDGES
-- ============================================================================

data EdgeLabel : Set where
  PRECEDES     : EdgeLabel  -- n₁ comes before n₂
  FOLLOWS      : EdgeLabel  -- n₁ comes after n₂
  CONTAINS     : EdgeLabel  -- n₁ contains n₂
  TRANSFORMS   : EdgeLabel  -- n₁ transforms into n₂
  OPPOSES      : EdgeLabel  -- n₁ opposes n₂
  MERGES       : EdgeLabel  -- n₁ merges with n₂
  SEPARATES    : EdgeLabel  -- n₁ separates from n₂
  REPEATS      : EdgeLabel  -- n₁ repeats n₂
  DISAPPEARS   : EdgeLabel  -- n₁ disappears
  REAPPEARS    : EdgeLabel  -- n₁ reappears
  INTERRUPTS   : EdgeLabel  -- n₁ interrupts n₂
  RESOLVES     : EdgeLabel  -- n₁ resolves n₂
  FAILS_TO_RESOLVE : EdgeLabel  -- n₁ fails to resolve n₂

-- Decision equality on edge labels
_≟ₑₗ_ : (a b : EdgeLabel) → Dec (a ≡ b)
PRECEDES ≟ₑₗ PRECEDES = yes refl
FOLLOWS ≟ₑₗ FOLLOWS = yes refl
CONTAINS ≟ₑₗ CONTAINS = yes refl
TRANSFORMS ≟ₑₗ TRANSFORMS = yes refl
OPPOSES ≟ₑₗ OPPOSES = yes refl
MERGES ≟ₑₗ MERGES = yes refl
SEPARATES ≟ₑₗ SEPARATES = yes refl
REPEATS ≟ₑₗ REPEATS = yes refl
DISAPPEARS ≟ₑₗ DISAPPEARS = yes refl
REAPPEARS ≟ₑₗ REAPPEARS = yes refl
INTERRUPTS ≟ₑₗ INTERRUPTS = yes refl
RESOLVES ≟ₑₗ RESOLVES = yes refl
FAILS_TO_RESOLVE ≟ₑₗ FAILS_TO_RESOLVE = yes refl
_ ≟ₑₗ _ = no λ ()

-- Labeled directed edge
record Edge : Set where
  constructor edge
  field
    source : NodeId
    target : NodeId
    label  : EdgeLabel
    timestamp : TemporalCoordinate
    -- INVARIANT: source ≠ target (no self-loops in formal model)
    no-self-loop : ¬(source ≡ target)

-- ============================================================================
-- POLICIES AND GATES (Formal Decidability)
-- ============================================================================

-- A gate is a decidable predicate on states
data Gate (State : Set) : Set where
  predicate : (test : State → Bool)
            → (dec : ∀ s → Dec (test s ≡ true))
            → Gate State

-- Execute a gate: deterministically decide passage
executeGate : {State : Set} → Gate State → State → Bool
executeGate (predicate test _) s = test s

-- Gate verdict with proof
gateVerdict : {State : Set} → (g : Gate State) → (s : State)
            → (executeGate g s ≡ true) ⊎ (executeGate g s ≡ false)
gateVerdict (predicate test dec) s =
  case (dec s) of λ where
    (yes h) → inl h
    (no ¬h) → inr (case (executeGate (predicate test dec) s) of λ b →
      case b of λ where
        true  → Empty.⊥-elim (¬h refl)
        false → refl)

-- Policy: a list of gates that must all pass
Policy : Set → Set
Policy State = List (Gate State)

-- Policy enforcement
allGatesPass : {State : Set} → Policy State → State → Bool
allGatesPass [] _ = true
allGatesPass (g ∷ gs) s = (executeGate g s) ∧ (allGatesPass gs s)

-- ============================================================================
-- PERSONAS AND COMPOSITION
-- ============================================================================

-- Persona represents a role with permissions and constraints
record Persona : Set where
  constructor persona
  field
    id : ℕ
    name : List ℕ  -- encoded name as list of nats
    permissions : List ℕ  -- permission codes
    constraints : List ℕ  -- constraint codes
    -- INVARIANT: permissions and constraints are non-empty
    perm-nonempty : length permissions > 0
    const-nonempty : length constraints > 0

-- Persona composition: merge two personas with invariant maintenance
composePersonas : Persona → Persona → Maybe Persona
composePersonas
  (persona id₁ n₁ p₁ c₁ perm₁ const₁)
  (persona id₂ n₂ p₂ c₂ perm₂ const₂) =
  let merged-perms = List.nub _≟ ℕ (p₁ ++ p₂)
      merged-consts = List.nub _≟ ℕ (c₁ ++ c₂)
  in if (length merged-perms > 0) ∧ (length merged-consts > 0)
     then just (persona (id₁ + id₂) (n₁ ++ n₂) merged-perms merged-consts
       (ℕ.zero<suc _) (ℕ.zero<suc _))
     else nothing

-- ============================================================================
-- TASKS AND ASSIGNMENTS
-- ============================================================================

data TaskStatus : Set where
  PENDING    : TaskStatus
  IN_PROGRESS : TaskStatus
  RESOLVED   : TaskStatus
  FAILED     : TaskStatus
  UNRESOLVED : TaskStatus

-- Decision equality on task status
_≟ₜₛ_ : (a b : TaskStatus) → Dec (a ≡ b)
PENDING ≟ₜₛ PENDING = yes refl
IN_PROGRESS ≟ₜₛ IN_PROGRESS = yes refl
RESOLVED ≟ₜₛ RESOLVED = yes refl
FAILED ≟ₜₛ FAILED = yes refl
UNRESOLVED ≟ₜₛ UNRESOLVED = yes refl
_ ≟ₜₛ _ = no λ ()

-- Task with formal properties
record Task : Set where
  constructor task
  field
    taskId : ℕ
    status : TaskStatus
    assignedTo : List ℕ  -- persona ids
    gatesDischarged : List ℕ  -- gate ids that have passed
    requirements : List ℕ  -- required gate ids
    -- INVARIANT: gatesDischarged ⊆ requirements
    gates-subset : ∀ g → List.Any (g ≡_) gatesDischarged
                        → List.Any (g ≡_) requirements

-- Task resolution: attempt to resolve a task by discharging remaining gates
resolveTask : Task → List ℕ → Maybe Task
resolveTask (task id st assigned discharged reqs inv) new-gates =
  let updated = List.nub _≟ ℕ (discharged ++ new-gates)
      all-discharged = List.all (λ g → List.any (g ≡?_) updated) reqs
  in if all-discharged
     then just (task id RESOLVED assigned updated reqs
       (λ g gm → List.Any.map (λ eq → Eq.trans eq (List.any-sound _ _ gm))
         (List.any-complete _ (List.any-sound _ _ gm))))
     else if List.any (λ g → List.any (g ≡?_) updated) reqs
          then just (task id IN_PROGRESS assigned updated reqs
            (λ g gm → List.Any.map (λ eq → Eq.trans eq (List.any-sound _ _ gm))
              (List.any-complete _ (List.any-sound _ _ gm))))
          else just (task id st assigned updated reqs
            (λ g gm → List.Any.map (λ eq → Eq.trans eq (List.any-sound _ _ gm))
              (List.any-complete _ (List.any-sound _ _ gm))))

-- ============================================================================
-- AUDIT LOG ENTRIES
-- ============================================================================

-- Audit event types
data AuditEventType : Set where
  GATE_DISCHARGE : AuditEventType
  PERSONA_MERGE : AuditEventType
  TASK_ASSIGNMENT : AuditEventType
  TASK_RESOLUTION : AuditEventType
  POLICY_VIOLATED : AuditEventType
  STATE_TRANSITION : AuditEventType

-- Decision equality on audit event types
_≟ₐₑₜ_ : (a b : AuditEventType) → Dec (a ≡ b)
GATE_DISCHARGE ≟ₐₑₜ GATE_DISCHARGE = yes refl
PERSONA_MERGE ≟ₐₑₜ PERSONA_MERGE = yes refl
TASK_ASSIGNMENT ≟ₐₑₜ TASK_ASSIGNMENT = yes refl
TASK_RESOLUTION ≟ₐₑₜ TASK_RESOLUTION = yes refl
POLICY_VIOLATED ≟ₐₑₜ POLICY_VIOLATED = yes refl
STATE_TRANSITION ≟ₐₑₜ STATE_TRANSITION = yes refl
_ ≟ₐₑₜ _ = no λ ()

-- Audit log entry with immutable chain of responsibility
record AuditEntry : Set where
  constructor audit-entry
  field
    sequence : ℕ  -- monotonically increasing
    timestamp : TemporalCoordinate
    eventType : AuditEventType
    actor : ℕ  -- persona id of who performed action
    action : List ℕ  -- encoded action parameters
    stateHash : ℕ  -- hash of system state after action
    previousHash : ℕ  -- hash of previous state (chain of custody)

-- ============================================================================
-- INTERRUPTION SET (Formal Unresolved States)
-- ============================================================================

-- Interruption markers
data InterruptionClass : Set where
  TEXT_INTERRUPTION : InterruptionClass
  IMAGE_INTERRUPTION : InterruptionClass
  DIALOGUE_INTERRUPTION : InterruptionClass
  TERMINAL_UNRESOLVED : InterruptionClass

-- Decision equality on interruption classes
_≟ᵢc_ : (a b : InterruptionClass) → Dec (a ≡ b)
TEXT_INTERRUPTION ≟ᵢc TEXT_INTERRUPTION = yes refl
IMAGE_INTERRUPTION ≟ᵢc IMAGE_INTERRUPTION = yes refl
DIALOGUE_INTERRUPTION ≟ᵢc DIALOGUE_INTERRUPTION = yes refl
TERMINAL_UNRESOLVED ≟ᵢc TERMINAL_UNRESOLVED = yes refl
_ ≟ᵢc _ = no λ ()

-- Formal interruption record
record Interruption : Set where
  constructor interruption
  field
    nodeId : NodeId
    class : InterruptionClass
    ambiguityMeasure : ℕ  -- |possible continuations|
    markedUnresolved : Bool  -- explicitly marked as unresolved
    remainingGates : List ℕ  -- gates not yet discharged

-- ============================================================================
-- SYSTEM STATE: Immutable snapshot
-- ============================================================================

record SystemState : Set where
  constructor state
  field
    nodes : List SymbolicNode
    edges : List Edge
    personas : List Persona
    tasks : List Task
    auditLog : List AuditEntry
    interruptions : List Interruption
    -- INVARIANT: auditLog is ordered by sequence number
    audit-ordered : ∀ i j → i < length auditLog → j < length auditLog → i < j
                           → (List.index auditLog (Fin.fromℕ< i)) .AuditEntry.sequence
                              < (List.index auditLog (Fin.fromℕ< j)) .AuditEntry.sequence

-- ============================================================================
-- HARDENER CONSTRAINTS: Fail-closed properties
-- ============================================================================

-- Fail-closed constraint: system rejects invalid operations
record FailClosedConstraint : Set where
  constructor constraint
  field
    name : List ℕ  -- constraint name
    test : SystemState → Bool
    proof : ∀ s → Dec (test s ≡ true)
    -- Invariant: test is deterministic and decidable
    deterministic : ∀ s → (test s ≡ true) ⊎ (test s ≡ false)

-- Execute all fail-closed constraints
allConstraintsSatisfied : List FailClosedConstraint → SystemState → Bool
allConstraintsSatisfied [] _ = true
allConstraintsSatisfied (c ∷ cs) s =
  (c .FailClosedConstraint.test s) ∧ (allConstraintsSatisfied cs s)

-- Rollback guarantee: state can revert to previous audit checkpoint
record RollbackPoint : Set where
  constructor rollback-point
  field
    checkpointSeq : ℕ
    checkpointState : SystemState
    -- Invariant: checkpoint sequence is strictly increasing
    is-checkpoint : checkpointSeq > 0

-- Iteration accountability: tracks all attempts and modifications
record IterationRecord : Set where
  constructor iteration-record
  field
    iteration : ℕ
    operationCount : ℕ
    gatesAttempted : List ℕ
    gatesPassed : List ℕ
    modifiedNodeIds : List NodeId
    -- INVARIANT: gatesPassed ⊆ gatesAttempted
    gates-passed-subset : ∀ g → List.Any (g ≡_) gatesPassed
                               → List.Any (g ≡_) gatesAttempted
