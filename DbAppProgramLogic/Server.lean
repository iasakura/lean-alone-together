import DbAppProgramLogic.Logic

namespace DbAppProgramLogic

/-!
Server-level and request-level correctness wrappers.

The core POPL'18 formalization stops at transaction programs and top-level RG validity. This file
adds a thin layer for talking about handlers, request families, commit logs, and server-style
parallel executions. The main results here explain final states in terms of commit-order traces.
-/

/-- Relational specification for one committed handler: pre-state to post-state. -/
abbrev StateSpec := Database → Database → Prop
abbrev StateTransformer := Database → Database
abbrev RequestSpec (Req : Type) := Req → StateSpec
abbrev RequestTransformer (Req : Type) := Req → StateTransformer
abbrev TxnIndexedRequestSpec (Req : Type) := Req → TxnId → StateSpec

namespace StateSpec

def graph (f : StateTransformer) : StateSpec :=
  fun db db' => db' = f db

end StateSpec

namespace RequestSpec

def assign {Req : Type} (requestOf : TxnId → Req) (specs : RequestSpec Req) : TxnId → StateSpec :=
  fun txnId => specs (requestOf txnId)

def hideTxnIds {Req : Type} (requestOf : TxnId → Req)
    (specs : TxnIndexedRequestSpec Req) : RequestSpec Req :=
  fun req db db' => ∃ txnId, requestOf txnId = req ∧ specs req txnId db db'

def graphAssign {Req : Type} (requestOf : TxnId → Req) (fs : RequestTransformer Req) :
    TxnId → StateSpec :=
  assign requestOf (fun req => StateSpec.graph (fs req))

end RequestSpec

namespace Server

open Logic

private def commandTag : Command ι σ → Nat
  | .skip => 0
  | .letE _ _ _ => 1
  | .ite _ _ _ => 2
  | .seq _ _ => 3
  | .insert _ => 4
  | .delete _ _ => 5
  | .select _ _ _ _ => 6
  | .update _ _ _ => 7
  | .foreach _ _ _ _ => 8
  | .foreachRuntime _ _ _ _ _ => 9
  | .txn _ _ _ => 10
  | .txnRuntime _ _ _ _ _ => 11
  | .par _ _ => 12

def NonParallel : Semantics.Program → Prop
  | .par _ _ => False
  | _ => True

inductive SingleTxnProgram (txnId : TxnId) : Semantics.Program → Prop where
  | txn {isolation : IsolationSpec Database} {body : Semantics.Program} :
      SingleTxnProgram txnId (.txn txnId isolation body)
  | runtime {isolation : IsolationSpec Database}
      {localDb snapshot : Database} {body : Semantics.Program} :
      SingleTxnProgram txnId (.txnRuntime txnId isolation localDb snapshot body)
  | skip :
      SingleTxnProgram txnId (Command.skip : Semantics.Program)

theorem singleTxn_nonParallel {txnId : TxnId} {program : Semantics.Program}
    (h : SingleTxnProgram txnId program) :
    NonParallel program := by
  cases h <;> simp [NonParallel]

/-- Quiescent programs for the server layer: all running branches have terminated. -/
inductive ProgramDone : Semantics.Program → Prop where
  | skip :
      ProgramDone (Command.skip : Semantics.Program)
  | par {left right : Semantics.Program} :
      ProgramDone left →
      ProgramDone right →
      ProgramDone (.par left right : Semantics.Program)

/-- A commit event lifted through nested `par` structure. This is the server-layer notion of "one
transaction has just committed". -/
inductive TxnCommitStep :
    TxnId → Semantics.Program → Database → Semantics.Program → Database → Prop where
  | root {txnId : TxnId} {isolation : IsolationSpec Database}
      {localDb snapshot currentDb : Database} :
      isolation.commit localDb snapshot currentDb →
      TxnCommitStep
        txnId
        (.txnRuntime txnId isolation localDb snapshot (Command.skip : Semantics.Program))
        currentDb
        (Command.skip : Semantics.Program)
        (Database.flush localDb currentDb)
  | parLeft {txnId : TxnId} {left left' right : Semantics.Program}
      {db db' : Database} :
      TxnCommitStep txnId left db left' db' →
      TxnCommitStep txnId (.par left right) db (.par left' right) db'
  | parRight {txnId : TxnId} {left right right' : Semantics.Program}
      {db db' : Database} :
      TxnCommitStep txnId right db right' db' →
      TxnCommitStep txnId (.par left right) db (.par left right') db'

inductive CommitSequence (specs : TxnId → StateSpec) :
    Database → List TxnId → Database → Prop where
  | nil {db : Database} :
      CommitSequence specs db [] db
  | cons {db db' db'' : Database} {txnId : TxnId} {rest : List TxnId} :
      specs txnId db db' →
      CommitSequence specs db' rest db'' →
      CommitSequence specs db (txnId :: rest) db''

structure CommitEvent where
  txnId : TxnId
  before : Database
  after : Database

inductive CommitLog (specs : TxnId → StateSpec) :
    Database → List CommitEvent → Database → Prop where
  | nil {db : Database} :
      CommitLog specs db [] db
  | cons {db db' db'' : Database} {txnId : TxnId} {rest : List CommitEvent} :
      specs txnId db db' →
      CommitLog specs db' rest db'' →
      CommitLog specs db ({ txnId := txnId, before := db, after := db' } :: rest) db''

namespace CommitSequence

theorem snoc {specs : TxnId → StateSpec}
    {db db' db'' : Database} {commits : List TxnId} {txnId : TxnId}
    (hSeq : CommitSequence specs db commits db')
    (hSpec : specs txnId db' db'') :
    CommitSequence specs db (commits ++ [txnId]) db'' := by
  induction hSeq with
  | nil =>
      simpa using CommitSequence.cons hSpec CommitSequence.nil
  | @cons db0 db1 db2 txnId' rest hHead hTail ih =>
      simp
      exact CommitSequence.cons hHead (ih hSpec)

theorem graph_iff_foldl {fs : TxnId → StateTransformer}
    {db db' : Database} {commits : List TxnId} :
    CommitSequence (fun txnId => StateSpec.graph (fs txnId)) db commits db' ↔
      db' = List.foldl (fun current txnId => fs txnId current) db commits := by
  constructor
  · intro hSeq
    induction hSeq with
    | nil =>
        simp
    | @cons db0 db1 db2 txnId rest hHead hTail ih =>
        rcases hHead with rfl
        simp [ih]
  · intro hEq
    induction commits generalizing db with
    | nil =>
        simp at hEq
        cases hEq
        exact CommitSequence.nil
    | cons txnId rest ih =>
        simp at hEq
        refine CommitSequence.cons ?_ (ih hEq)
        rfl

end CommitSequence

namespace CommitLog

def txnIds (events : List CommitEvent) : List TxnId :=
  events.map CommitEvent.txnId

def requests {Req : Type} (requestOf : TxnId → Req) (events : List CommitEvent) : List Req :=
  events.map (fun event => requestOf event.txnId)

theorem ofCommitSequence {specs : TxnId → StateSpec}
    {db db' : Database} {commits : List TxnId}
    (hSeq : CommitSequence specs db commits db') :
    ∃ events, CommitLog specs db events db' := by
  induction hSeq with
  | nil =>
      exact ⟨[], CommitLog.nil⟩
  | @cons db0 db1 db2 txnId rest hHead hTail ih =>
      rcases ih with ⟨events, hLog⟩
      exact ⟨{ txnId := txnId, before := db0, after := db1 } :: events,
        CommitLog.cons hHead hLog⟩

theorem toCommitSequence {specs : TxnId → StateSpec}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog specs db events db') :
    ∃ commits : List TxnId, CommitSequence specs db commits db' := by
  induction hLog with
  | nil =>
      exact ⟨[], CommitSequence.nil⟩
  | @cons db0 db1 db2 txnId rest hHead hTail ih =>
      rcases ih with ⟨commits, hSeq⟩
      exact ⟨txnId :: commits, CommitSequence.cons hHead hSeq⟩

theorem events_match_specs {specs : TxnId → StateSpec}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog specs db events db') :
    ∀ event ∈ events, specs event.txnId event.before event.after := by
  intro event hMem
  induction hLog generalizing event with
  | nil =>
      cases hMem
  | @cons db0 db1 db2 txnId rest hHead hTail ih =>
      simp at hMem
      rcases hMem with hEq | hIn
      · cases hEq
        exact hHead
      · exact ih _ hIn

theorem graph_implies_eventEq {fs : TxnId → StateTransformer}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog (fun txnId => StateSpec.graph (fs txnId)) db events db') :
    ∀ event ∈ events, event.after = fs event.txnId event.before := by
  intro event hMem
  exact events_match_specs hLog event hMem

theorem graph_implies_foldl {fs : TxnId → StateTransformer}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog (fun txnId => StateSpec.graph (fs txnId)) db events db') :
    db' = List.foldl (fun current event => fs event.txnId current) db events := by
  induction hLog with
  | nil =>
      simp
  | @cons db0 db1 db2 txnId rest hHead hTail ih =>
      rcases hHead with rfl
      simp [ih]

theorem graphAssign_implies_foldl_requests {Req : Type} {requestOf : TxnId → Req}
    {fs : RequestTransformer Req}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog (RequestSpec.graphAssign requestOf fs) db events db') :
    db' = List.foldl (fun current req => fs req current) db (requests requestOf events) := by
  induction hLog with
  | nil =>
      simp [requests]
  | @cons db0 db1 db2 txnId rest hHead hTail ih =>
      rcases hHead with rfl
      simp [requests, ih, RequestSpec.graphAssign, RequestSpec.assign]

theorem graphAssign_implies_eventEq {Req : Type} {requestOf : TxnId → Req}
    {fs : RequestTransformer Req}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog (RequestSpec.graphAssign requestOf fs) db events db') :
    ∀ event ∈ events, event.after = fs (requestOf event.txnId) event.before := by
  intro event hMem
  exact events_match_specs hLog event hMem

theorem requests_match_specs {Req : Type} {requestOf : TxnId → Req}
    {specs : RequestSpec Req}
    {db db' : Database} {events : List CommitEvent}
    (hLog : CommitLog (RequestSpec.assign requestOf specs) db events db') :
    ∀ event ∈ events, specs (requestOf event.txnId) event.before event.after := by
  intro event hMem
  exact events_match_specs hLog event hMem

end CommitLog

theorem TxnCommitStep.step {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (h : TxnCommitStep txnId program db program' db') :
    Semantics.Step program db program' db' := by
  induction h with
  | root hCommit =>
      exact Semantics.Step.txnCommit hCommit
  | parLeft hCommit ih =>
      exact Semantics.Step.parLeft ih
  | parRight hCommit ih =>
      exact Semantics.Step.parRight ih

theorem TxnCommitStep.ne_refreshVisible {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (h : TxnCommitStep txnId program db program' db') :
    program' ≠ refreshVisible program db' := by
  induction h with
  | root =>
      simp [refreshVisible]
  | parLeft hInner ih =>
      simp [refreshVisible, ih]
  | parRight hInner ih =>
      simp [refreshVisible, ih]

theorem TxnCommitStep.ne_self {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (h : TxnCommitStep txnId program db program' db') :
    program' ≠ program := by
  induction h with
  | root =>
      simp
  | parLeft hInner ih =>
      simp [ih]
  | parRight hInner ih =>
      simp [ih]

theorem localStep_changes_cmd {snapshot : Database} {txnId : TxnId}
    {cmd cmd' : Command ι Database} {localDb localDb' : Database}
    (h : Semantics.LocalStep snapshot txnId cmd localDb cmd' localDb') :
    cmd' ≠ cmd := by
  induction h with
  | letE hEval =>
      rename_i x expr body value localDb
      intro hEq
      cases body <;> simp [Command.subst] at hEq
      case letE y expr' body' =>
        rcases hEq with ⟨rfl, _hExpr, hRec⟩
        simp at hRec
        have hPos : 0 < 1 + sizeOf y + sizeOf expr' := by
          have h1le : 1 ≤ 1 + sizeOf y := by exact Nat.le_add_right 1 (sizeOf y)
          have h1 : 0 < 1 + sizeOf y := Nat.lt_of_lt_of_le Nat.zero_lt_one h1le
          exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
        have hLt : sizeOf body' < sizeOf (Command.letE y expr' body') := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_right hPos :
              sizeOf body' < sizeOf body' + (1 + sizeOf y + sizeOf expr'))
        rw [← hRec] at hLt
        simpa using hLt
  | iteTrue hEval =>
      rename_i condition thenBranch elseBranch localDb
      intro hEq
      cases thenBranch <;> simp [Command.subst] at hEq
      case ite condition' thenBranch' elseBranch' =>
        rcases hEq with ⟨rfl, hRec, _hElse⟩
        have hPos : 0 < 1 + sizeOf condition' + sizeOf elseBranch' := by
          have h1le : 1 ≤ 1 + sizeOf condition' := by exact Nat.le_add_right 1 (sizeOf condition')
          have h1 : 0 < 1 + sizeOf condition' := Nat.lt_of_lt_of_le Nat.zero_lt_one h1le
          exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
        have hLt : sizeOf thenBranch' < sizeOf (Command.ite condition' thenBranch' elseBranch') := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_right hPos :
              sizeOf thenBranch' < sizeOf thenBranch' + (1 + sizeOf condition' + sizeOf elseBranch'))
        rw [← hRec] at hLt
        simpa using hLt
  | iteFalse hEval =>
      rename_i condition thenBranch elseBranch localDb
      intro hEq
      cases elseBranch <;> simp [Command.subst] at hEq
      case ite condition' thenBranch' elseBranch' =>
        rcases hEq with ⟨rfl, _hThen, hRec⟩
        have hPos : 0 < 1 + sizeOf condition' + sizeOf thenBranch' := by
          have h1le : 1 ≤ 1 + sizeOf condition' := by exact Nat.le_add_right 1 (sizeOf condition')
          have h1 : 0 < 1 + sizeOf condition' := Nat.lt_of_lt_of_le Nat.zero_lt_one h1le
          exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
        have hLt : sizeOf elseBranch' < sizeOf (Command.ite condition' thenBranch' elseBranch') := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_right hPos :
              sizeOf elseBranch' < sizeOf elseBranch' + (1 + sizeOf condition' + sizeOf thenBranch'))
        rw [← hRec] at hLt
        simpa using hLt
  | seqLeft hInner ih =>
      intro hEq
      injection hEq with hEqLeft _hEqRight
      exact ih hEqLeft
  | seqSkip =>
      rename_i next localDb
      intro hEq
      cases next <;> simp at hEq
      case seq left right =>
        rcases hEq with ⟨rfl, hRec⟩
        have hLt : sizeOf right < sizeOf (Command.seq Command.skip right) := by simp
        rw [← hRec] at hLt
        simpa using hLt
  | insert hEval hFresh =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | select hCollect =>
      rename_i binder source predicate body selected localDb
      intro hEq
      cases body <;> simp [Command.subst] at hEq
      case select binder' source' predicate' body' =>
        rcases hEq with ⟨rfl, rfl, _hPred, hRec⟩
        simp at hRec
        have hPos : 0 < 1 + sizeOf binder' + sizeOf source' + sizeOf predicate' := by
          have h1le : 1 ≤ 1 + sizeOf binder' := by exact Nat.le_add_right 1 (sizeOf binder')
          have h1 : 0 < 1 + sizeOf binder' := Nat.lt_of_lt_of_le Nat.zero_lt_one h1le
          have h2 : 1 + sizeOf binder' ≤ 1 + sizeOf binder' + sizeOf source' := by
            exact Nat.le_add_right _ _
          have h3 :
              1 + sizeOf binder' + sizeOf source' ≤
                1 + sizeOf binder' + sizeOf source' + sizeOf predicate' := by
            exact Nat.le_add_right _ _
          exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) h3
        have hLt : sizeOf body' < sizeOf (Command.select binder' source' predicate' body') := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_right hPos :
              sizeOf body' < sizeOf body' + (1 + sizeOf binder' + sizeOf source' + sizeOf predicate'))
        rw [← hRec] at hLt
        simpa using hLt
  | delete hCollect hDisjoint =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | update hCollect hDisjoint =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | foreachStart hEval =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | foreachNext =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | foreachDone =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag

theorem step_changes_program
    {program program' : Semantics.Program} {db db' : Database}
    (h : Semantics.Step program db program' db') :
    program' ≠ program := by
  induction h with
  | txnStart =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | txnExec hExec hLocal =>
      intro hEq
      injection hEq with _hTxnId _hIsolation hLocalEq hSnapEq hBodyEq
      exact localStep_changes_cmd hLocal hBodyEq
  | txnCommit =>
      intro hEq
      have hTag := congrArg commandTag hEq
      simp [commandTag] at hTag
  | parLeft hInner ih =>
      intro hEq
      injection hEq with hEqLeft _hEqRight
      exact ih hEqLeft
  | parRight hInner ih =>
      intro hEq
      injection hEq with _hEqLeft hEqRight
      exact ih hEqRight

/-- Every actual step is either a transaction commit lifted through `par`, or definitely not one.
This is the structural classification needed to isolate the first commit in a parallel trace. -/
theorem step_noCommit_or_commit
    {program program' : Semantics.Program} {db db' : Database}
    (h : Semantics.Step program db program' db') :
    (¬ ∃ txnId, TxnCommitStep txnId program db program' db') ∨
      ∃ txnId, TxnCommitStep txnId program db program' db' := by
  induction h with
  | txnStart =>
      left
      intro hCommit
      rcases hCommit with ⟨txnId, hCommit⟩
      cases hCommit
  | txnExec hExec hLocal =>
      left
      intro hCommit
      rcases hCommit with ⟨txnId, hCommit⟩
      cases hCommit
  | txnCommit hCommit =>
      right
      exact ⟨_, TxnCommitStep.root hCommit⟩
  | parLeft hInner ih =>
      cases ih with
      | inl hNoInner =>
          left
          intro hCommit
          rcases hCommit with ⟨txnId, hCommit⟩
          cases hCommit with
          | parLeft hInnerCommit =>
              exact hNoInner ⟨txnId, hInnerCommit⟩
          | parRight hRightCommit =>
              exact step_changes_program hInner rfl
      | inr hInnerCommit =>
          right
          rcases hInnerCommit with ⟨txnId, hInnerCommit⟩
          exact ⟨txnId, TxnCommitStep.parLeft hInnerCommit⟩
  | parRight hInner ih =>
      cases ih with
      | inl hNoInner =>
          left
          intro hCommit
          rcases hCommit with ⟨txnId, hCommit⟩
          cases hCommit with
          | parLeft hLeftCommit =>
              exact step_changes_program hInner rfl
          | parRight hInnerCommit =>
              exact hNoInner ⟨txnId, hInnerCommit⟩
      | inr hInnerCommit =>
          right
          rcases hInnerCommit with ⟨txnId, hInnerCommit⟩
          exact ⟨txnId, TxnCommitStep.parRight hInnerCommit⟩

/-- Inverting a commit through one layer of `par`: the commit must come from either the left or the
right branch. This is the structural fact used in the TR proof of RG-Par when focusing on the
transaction that commits first. -/
theorem txnCommitStep_par_inv {txnId : TxnId}
    {left right program' : Semantics.Program} {db db' : Database}
    (h : TxnCommitStep txnId (.par left right) db program' db') :
    (∃ left', program' = (.par left' right : Semantics.Program) ∧
      TxnCommitStep txnId left db left' db') ∨
      (∃ right', program' = (.par left right' : Semantics.Program) ∧
        TxnCommitStep txnId right db right' db') := by
  cases h with
  | parLeft hInner =>
      exact Or.inl ⟨_, rfl, hInner⟩
  | parRight hInner =>
      exact Or.inr ⟨_, rfl, hInner⟩

theorem respectsRely_implies {R : Rely}
    {program : Semantics.Program} {db db' : Database}
    (h : respectsRely R program db db') :
    R db db' := by
  induction program generalizing db db' with
  | txnRuntime txnId isolation localDb snapshot body =>
      by_cases hBody : body = (Command.skip : Semantics.Program)
      · subst hBody
        have hPair : R db db' ∧ isolation.commit localDb snapshot db' := by
          simpa [respectsRely] using h
        exact hPair.1
      · have hPair : R db db' ∧ isolation.exec localDb snapshot db' := by
          simpa [respectsRely, hBody] using h
        exact hPair.1
  | par left right ihLeft ihRight =>
      have hPair : respectsRely R left db db' ∧ respectsRely R right db db' := by
        simpa [respectsRely] using h
      exact ihLeft hPair.1
  | _ =>
      simpa [respectsRely] using h

theorem step_sameDb_or_commit
    {program program' : Semantics.Program} {db db' : Database}
    (h : Semantics.Step program db program' db') :
    db' = db ∨ ∃ txnId, TxnCommitStep txnId program db program' db' := by
  induction h with
  | txnStart =>
      exact Or.inl rfl
  | txnExec =>
      exact Or.inl rfl
  | txnCommit hCommit =>
      exact Or.inr ⟨_, TxnCommitStep.root hCommit⟩
  | parLeft hStep ih =>
      cases ih with
      | inl hEq =>
          exact Or.inl hEq
      | inr hCommit =>
          rcases hCommit with ⟨txnId, hCommit⟩
          exact Or.inr ⟨txnId, TxnCommitStep.parLeft hCommit⟩
  | parRight hStep ih =>
      cases ih with
      | inl hEq =>
          exact Or.inl hEq
      | inr hCommit =>
          rcases hCommit with ⟨txnId, hCommit⟩
          exact Or.inr ⟨txnId, TxnCommitStep.parRight hCommit⟩

theorem globalInterleavedStep_preservesInvariant_of_commitSpecs
    {I : Assertion} {R : Rely} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hCommitSpec :
      ∀ {txnId program db program' db'},
        TxnCommitStep txnId program db program' db' →
        specs txnId db db')
    (hPreserve :
      ∀ txnId db db', I db → specs txnId db db' → I db')
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg') :
    I cfg.globalDb →
    I cfg'.globalDb := by
  intro hI
  cases hStep with
  | inl hActual =>
      rcases step_sameDb_or_commit hActual with hEq | hCommit
      · simpa [hEq] using hI
      · rcases hCommit with ⟨txnId, hCommit⟩
        exact hPreserve txnId _ _ hI (hCommitSpec hCommit)
  | inr hRely =>
      rcases hRely with ⟨_hProgram, hRespect⟩
      exact hStable _ _ hI (respectsRely_implies hRespect)

theorem globalInterleavedStep_project_left_noncommit {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStep R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStep R ⟨left, db⟩ ⟨left', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              exact globalMultiStep_single R hInner
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              exact MultiStep.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hRespect⟩
      refine ⟨refreshVisible left db', refreshVisible right db', hProgram, ?_⟩
      exact MultiStep.tail MultiStep.refl (Or.inr ⟨rfl, hRespect.1⟩)

theorem globalInterleavedStep_project_right_noncommit {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStep R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStep R ⟨right, db⟩ ⟨right', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              exact MultiStep.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              exact globalMultiStep_single R hInner
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hRespect⟩
      refine ⟨refreshVisible left db', refreshVisible right db', hProgram, ?_⟩
      exact MultiStep.tail MultiStep.refl (Or.inr ⟨rfl, hRespect.2⟩)

theorem globalInterleavedStep_sameDb_or_commit {R : Rely}
    (hSilent : ∀ db db', R db db' → db' = db)
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg') :
    cfg'.globalDb = cfg.globalDb ∨
      ∃ txnId, TxnCommitStep txnId cfg.program cfg.globalDb cfg'.program cfg'.globalDb := by
  cases hStep with
  | inl hActual =>
      exact step_sameDb_or_commit hActual
  | inr hRely =>
      rcases hRely with ⟨_hProgram, hRespect⟩
      left
      exact hSilent _ _ (respectsRely_implies hRespect)

theorem globalMultiStep_preservesInvariant_of_commitSpecs
    {I : Assertion} {R : Rely} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hCommitSpec :
      ∀ {txnId program db program' db'},
        TxnCommitStep txnId program db program' db' →
        specs txnId db db')
    (hPreserve :
      ∀ txnId db db', I db → specs txnId db db' → I db')
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg)
    (hI : I db) :
    I finalCfg.globalDb := by
  induction hRun with
  | refl =>
      simpa using hI
  | tail hPrev hLast ih =>
      exact globalInterleavedStep_preservesInvariant_of_commitSpecs
        hStable hCommitSpec hPreserve hLast ih

inductive CommitFreeGlobalMultiStep (R : Rely) :
    GlobalConfig → GlobalConfig → Prop where
  | refl {cfg : GlobalConfig} :
      CommitFreeGlobalMultiStep R cfg cfg
  | tail {cfg₁ cfg₂ cfg₃ : GlobalConfig} :
      CommitFreeGlobalMultiStep R cfg₁ cfg₂ →
      globalInterleavedStep R cfg₂ cfg₃ →
      (¬ ∃ txnId, TxnCommitStep txnId cfg₂.program cfg₂.globalDb cfg₃.program cfg₃.globalDb) →
      CommitFreeGlobalMultiStep R cfg₁ cfg₃

theorem CommitFreeGlobalMultiStep.toMultiStep {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (h : CommitFreeGlobalMultiStep R cfg₁ cfg₂) :
    GlobalMultiStep R cfg₁ cfg₂ := by
  induction h with
  | refl =>
      exact MultiStep.refl
  | tail hPrev hStep hNoCommit ih =>
      exact MultiStep.tail ih hStep

theorem globalMultiStep_split_first_commit {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂) :
    CommitFreeGlobalMultiStep R cfg₁ cfg₂ ∨
      ∃ midCfg nextCfg txnId,
        CommitFreeGlobalMultiStep R cfg₁ midCfg ∧
        globalInterleavedStep R midCfg nextCfg ∧
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextCfg.program nextCfg.globalDb ∧
        GlobalMultiStep R nextCfg cfg₂ := by
  induction hRun with
  | refl =>
      exact Or.inl CommitFreeGlobalMultiStep.refl
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases ih with
      | inl hCommitFree =>
          cases hLast with
          | inl hActual =>
              cases step_noCommit_or_commit hActual with
              | inl hNoCommit =>
                  exact Or.inl (CommitFreeGlobalMultiStep.tail hCommitFree (Or.inl hActual) hNoCommit)
              | inr hCommit =>
                  rcases hCommit with ⟨txnId, hCommit⟩
                  exact Or.inr ⟨cfgMid, cfgFinal, txnId, hCommitFree, Or.inl hActual, hCommit,
                    MultiStep.refl⟩
          | inr hRely =>
              have hNoCommit :
                  ¬ ∃ txnId,
                    TxnCommitStep txnId
                      cfgMid.program
                      cfgMid.globalDb
                      cfgFinal.program
                      cfgFinal.globalDb := by
                intro hCommit
                rcases hCommit with ⟨txnId, hCommit⟩
                rcases hRely with ⟨hProgram, _hRespect⟩
                exact TxnCommitStep.ne_refreshVisible hCommit hProgram
              exact Or.inl (CommitFreeGlobalMultiStep.tail hCommitFree (Or.inr hRely) hNoCommit)
      | inr hSplit =>
          rcases hSplit with ⟨midCfg, nextCfg, txnId, hCommitFree, hFirstStep, hFirstCommit, hTail⟩
          exact Or.inr ⟨midCfg, nextCfg, txnId, hCommitFree, hFirstStep, hFirstCommit,
            MultiStep.tail hTail hLast⟩

theorem commitFreeGlobalMultiStep_project_left {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStep R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStep R ⟨left, db⟩ ⟨left', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, MultiStep.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hLeftRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStep_project_left_noncommit hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hLeftStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram, MultiStep.trans hLeftRun hLeftStep⟩

theorem commitFreeGlobalMultiStep_project_right {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStep R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStep R ⟨right, db⟩ ⟨right', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, MultiStep.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hRightRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStep_project_right_noncommit hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hRightStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram, MultiStep.trans hRightRun hRightStep⟩

/-- View theorem for the first commit after a commit-free parallel prefix. Up to the first commit,
the sibling branch can be erased; the commit itself then comes from one side exactly as in the TR
proof of RG-Par. -/
theorem commitFreePrefix_firstCommit_view {R : Rely}
    {left right : Semantics.Program} {db : Database}
    {midCfg : GlobalConfig} {nextProgram : Semantics.Program} {nextDb : Database}
    {txnId : TxnId}
    (hPrefix :
      CommitFreeGlobalMultiStep R
        ⟨(.par left right : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep txnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    (∃ leftMid rightMid leftNext,
      midCfg.program = (.par leftMid rightMid : Semantics.Program) ∧
      GlobalMultiStep R ⟨left, db⟩ ⟨leftMid, midCfg.globalDb⟩ ∧
      TxnCommitStep txnId leftMid midCfg.globalDb leftNext nextDb ∧
      nextProgram = (.par leftNext rightMid : Semantics.Program)) ∨
      (∃ leftMid rightMid rightNext,
        midCfg.program = (.par leftMid rightMid : Semantics.Program) ∧
        GlobalMultiStep R ⟨right, db⟩ ⟨rightMid, midCfg.globalDb⟩ ∧
        TxnCommitStep txnId rightMid midCfg.globalDb rightNext nextDb ∧
        nextProgram = (.par leftMid rightNext : Semantics.Program)) := by
  rcases commitFreeGlobalMultiStep_project_left hPrefix with
    ⟨leftMid, rightMid, hMidProgram, hLeftRun⟩
  rcases commitFreeGlobalMultiStep_project_right hPrefix with
    ⟨leftMid', rightMid', hMidProgram', hRightRun⟩
  have hSame :
      (.par leftMid rightMid : Semantics.Program) =
        (.par leftMid' rightMid' : Semantics.Program) := by
    simpa [hMidProgram] using hMidProgram'
  cases hSame
  have hCommit' :
      TxnCommitStep txnId
        (.par leftMid rightMid : Semantics.Program)
        midCfg.globalDb
        nextProgram
        nextDb := by
    simpa [hMidProgram] using hCommit
  rcases txnCommitStep_par_inv hCommit' with hLeftCommit | hRightCommit
  · rcases hLeftCommit with ⟨leftNext, hNextProgram, hLeftCommit⟩
    exact Or.inl ⟨leftMid, rightMid, leftNext, hMidProgram, hLeftRun, hLeftCommit, hNextProgram⟩
  · rcases hRightCommit with ⟨rightNext, hNextProgram, hRightCommit⟩
    exact Or.inr ⟨leftMid, rightMid, rightNext, hMidProgram, hRightRun, hRightCommit, hNextProgram⟩

/-- TR-faithful invariant preservation for one interleaved step. The rely branch now changes only the
outer database, so this is the direct analogue of the paper's Appendix C definition. -/
theorem globalInterleavedStepTR_preservesInvariant_of_commitSpecs
    {I : Assertion} {R : Rely} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hCommitSpec :
      ∀ {txnId program db program' db'},
        TxnCommitStep txnId program db program' db' →
        specs txnId db db')
    (hPreserve :
      ∀ txnId db db', I db → specs txnId db db' → I db')
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStepTR R cfg cfg') :
    I cfg.globalDb →
    I cfg'.globalDb := by
  intro hI
  cases hStep with
  | inl hActual =>
      rcases step_sameDb_or_commit hActual with hEq | hCommit
      · simpa [hEq] using hI
      · rcases hCommit with ⟨txnId, hCommit⟩
        exact hPreserve txnId _ _ hI (hCommitSpec hCommit)
  | inr hRely =>
      rcases hRely with ⟨_hProgram, hR⟩
      exact hStable _ _ hI hR

theorem globalInterleavedStepTR_project_left_noncommit {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨left, db⟩ ⟨left', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              exact MultiStep.tail MultiStep.refl (Or.inl hInner)
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              exact MultiStep.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨left, right, ?_, ?_⟩
      · simpa using hProgram
      · exact MultiStep.tail MultiStep.refl (Or.inr ⟨rfl, hR⟩)

theorem globalInterleavedStepTR_project_right_noncommit {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨right, db⟩ ⟨right', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              exact MultiStep.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              exact MultiStep.tail MultiStep.refl (Or.inl hInner)
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨left, right, ?_, ?_⟩
      · simpa using hProgram
      · exact MultiStep.tail MultiStep.refl (Or.inr ⟨rfl, hR⟩)

theorem globalInterleavedStepTR_sameDb_or_commit {R : Rely}
    (hSilent : ∀ db db', R db db' → db' = db)
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStepTR R cfg cfg') :
    cfg'.globalDb = cfg.globalDb ∨
      ∃ txnId, TxnCommitStep txnId cfg.program cfg.globalDb cfg'.program cfg'.globalDb := by
  cases hStep with
  | inl hActual =>
      exact step_sameDb_or_commit hActual
  | inr hRely =>
      rcases hRely with ⟨_hProgram, hR⟩
      left
      exact hSilent _ _ hR

inductive CommitFreeGlobalMultiStepTR (R : Rely) :
    GlobalConfig → GlobalConfig → Prop where
  | refl {cfg : GlobalConfig} :
      CommitFreeGlobalMultiStepTR R cfg cfg
  | tail {cfg₁ cfg₂ cfg₃ : GlobalConfig} :
      CommitFreeGlobalMultiStepTR R cfg₁ cfg₂ →
      globalInterleavedStepTR R cfg₂ cfg₃ →
      (¬ ∃ txnId, TxnCommitStep txnId cfg₂.program cfg₂.globalDb cfg₃.program cfg₃.globalDb) →
      CommitFreeGlobalMultiStepTR R cfg₁ cfg₃

theorem CommitFreeGlobalMultiStepTR.toMultiStep {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (h : CommitFreeGlobalMultiStepTR R cfg₁ cfg₂) :
    GlobalMultiStepTR R cfg₁ cfg₂ := by
  induction h with
  | refl =>
      exact MultiStep.refl
  | tail hPrev hStep _hNoCommit ih =>
      exact MultiStep.tail ih hStep

theorem CommitFreeGlobalMultiStepTR.trans {R : Rely}
    {cfg₁ cfg₂ cfg₃ : GlobalConfig}
    (h₁ : CommitFreeGlobalMultiStepTR R cfg₁ cfg₂)
    (h₂ : CommitFreeGlobalMultiStepTR R cfg₂ cfg₃) :
    CommitFreeGlobalMultiStepTR R cfg₁ cfg₃ := by
  revert h₁
  induction h₂ with
  | refl =>
      intro h₁
      exact h₁
  | tail hPrev hStep hNoCommit ih =>
      intro h₁
      exact CommitFreeGlobalMultiStepTR.tail (ih h₁) hStep hNoCommit

theorem globalInterleavedStepTR_project_left_noncommit_commitFree {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      CommitFreeGlobalMultiStepTR R ⟨left, db⟩ ⟨left', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              refine CommitFreeGlobalMultiStepTR.tail CommitFreeGlobalMultiStepTR.refl (Or.inl hInner) ?_
              intro hCommit
              rcases hCommit with ⟨txnId, hCommit⟩
              exact hNoCommit ⟨txnId, TxnCommitStep.parLeft hCommit⟩
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              exact CommitFreeGlobalMultiStepTR.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨left, right, ?_, ?_⟩
      · simpa using hProgram
      · refine CommitFreeGlobalMultiStepTR.tail CommitFreeGlobalMultiStepTR.refl (Or.inr ⟨rfl, hR⟩) ?_
        intro hCommit
        rcases hCommit with ⟨txnId, hCommit⟩
        exact TxnCommitStep.ne_self hCommit rfl

theorem globalInterleavedStepTR_project_right_noncommit_commitFree {R : Rely}
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        ⟨program', db'⟩)
    (hNoCommit :
      ¬ ∃ txnId,
        TxnCommitStep txnId
          (.par left right : Semantics.Program)
          db
          program'
          db') :
    ∃ left' right',
      program' = (.par left' right' : Semantics.Program) ∧
      CommitFreeGlobalMultiStepTR R ⟨right, db⟩ ⟨right', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨_, right, rfl, ?_⟩
              subst hEq
              exact CommitFreeGlobalMultiStepTR.refl
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parLeft hCommit⟩
      | parRight hInner =>
          cases step_sameDb_or_commit hInner with
          | inl hEq =>
              refine ⟨left, _, rfl, ?_⟩
              subst hEq
              refine CommitFreeGlobalMultiStepTR.tail CommitFreeGlobalMultiStepTR.refl (Or.inl hInner) ?_
              intro hCommit
              rcases hCommit with ⟨txnId, hCommit⟩
              exact hNoCommit ⟨txnId, TxnCommitStep.parRight hCommit⟩
          | inr hCommit =>
              rcases hCommit with ⟨txnId, hCommit⟩
              exfalso
              apply hNoCommit
              exact ⟨txnId, TxnCommitStep.parRight hCommit⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨left, right, ?_, ?_⟩
      · simpa using hProgram
      · refine CommitFreeGlobalMultiStepTR.tail CommitFreeGlobalMultiStepTR.refl (Or.inr ⟨rfl, hR⟩) ?_
        intro hCommit
        rcases hCommit with ⟨txnId, hCommit⟩
        exact TxnCommitStep.ne_self hCommit rfl

theorem globalMultiStepTR_preservesInvariant_of_commitSpecs
    {I : Assertion} {R : Rely} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hCommitSpec :
      ∀ {txnId program db program' db'},
        TxnCommitStep txnId program db program' db' →
        specs txnId db db')
    (hPreserve :
      ∀ txnId db db', I db → specs txnId db db' → I db')
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg)
    (hI : I db) :
    I finalCfg.globalDb := by
  induction hRun with
  | refl =>
      simpa using hI
  | tail hPrev hLast ih =>
      exact globalInterleavedStepTR_preservesInvariant_of_commitSpecs
        hStable hCommitSpec hPreserve hLast ih

theorem globalMultiStepTR_split_first_commit {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStepTR R cfg₁ cfg₂) :
    CommitFreeGlobalMultiStepTR R cfg₁ cfg₂ ∨
      ∃ midCfg nextCfg txnId,
        CommitFreeGlobalMultiStepTR R cfg₁ midCfg ∧
        globalInterleavedStepTR R midCfg nextCfg ∧
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextCfg.program nextCfg.globalDb ∧
        GlobalMultiStepTR R nextCfg cfg₂ := by
  induction hRun with
  | refl =>
      exact Or.inl CommitFreeGlobalMultiStepTR.refl
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases ih with
      | inl hCommitFree =>
          cases hLast with
          | inl hActual =>
              cases step_noCommit_or_commit hActual with
              | inl hNoCommit =>
                  exact Or.inl (CommitFreeGlobalMultiStepTR.tail hCommitFree (Or.inl hActual) hNoCommit)
              | inr hCommit =>
                  rcases hCommit with ⟨txnId, hCommit⟩
                  exact Or.inr ⟨cfgMid, cfgFinal, txnId, hCommitFree, Or.inl hActual, hCommit,
                    MultiStep.refl⟩
          | inr hRely =>
              have hNoCommit :
                  ¬ ∃ txnId,
                    TxnCommitStep txnId
                      cfgMid.program
                      cfgMid.globalDb
                      cfgFinal.program
                      cfgFinal.globalDb := by
                intro hCommit
                rcases hCommit with ⟨txnId, hCommit⟩
                rcases hRely with ⟨hProgram, _hRespect⟩
                exact TxnCommitStep.ne_self hCommit hProgram
              exact Or.inl (CommitFreeGlobalMultiStepTR.tail hCommitFree (Or.inr hRely) hNoCommit)
      | inr hSplit =>
          rcases hSplit with ⟨midCfg, nextCfg, txnId, hCommitFree, hFirstStep, hFirstCommit, hTail⟩
          exact Or.inr ⟨midCfg, nextCfg, txnId, hCommitFree, hFirstStep, hFirstCommit,
            MultiStep.tail hTail hLast⟩

theorem commitFreeGlobalMultiStepTR_project_left {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨left, db⟩ ⟨left', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, MultiStep.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hLeftRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStepTR_project_left_noncommit hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hLeftStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram, MultiStep.trans hLeftRun hLeftStep⟩

theorem commitFreeGlobalMultiStepTR_project_right {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨right, db⟩ ⟨right', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, MultiStep.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hRightRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStepTR_project_right_noncommit hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hRightStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram, MultiStep.trans hRightRun hRightStep⟩

theorem commitFreeGlobalMultiStepTR_project_left_commitFree {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      CommitFreeGlobalMultiStepTR R ⟨left, db⟩ ⟨left', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, CommitFreeGlobalMultiStepTR.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hLeftRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStepTR_project_left_noncommit_commitFree hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hLeftStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram,
            CommitFreeGlobalMultiStepTR.trans hLeftRun hLeftStep⟩

theorem commitFreeGlobalMultiStepTR_project_right_commitFree {R : Rely}
    {left right : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      CommitFreeGlobalMultiStepTR R ⟨right, db⟩ ⟨right', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, CommitFreeGlobalMultiStepTR.refl⟩
  | tail hPrev hStep hNoCommit ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgram midDb =>
          rcases ih with ⟨midLeft, midRight, hMidProgram, hRightRun⟩
          have hMidProgram' : midProgram = (.par midLeft midRight : Semantics.Program) := by
            simpa using hMidProgram
          subst hMidProgram'
          rcases globalInterleavedStepTR_project_right_noncommit_commitFree hStep hNoCommit with
            ⟨nextLeft, nextRight, hNextProgram, hRightStep⟩
          exact ⟨nextLeft, nextRight, hNextProgram,
            CommitFreeGlobalMultiStepTR.trans hRightRun hRightStep⟩

theorem commitFreePrefix_firstCommit_viewTR {R : Rely}
    {left right : Semantics.Program} {db : Database}
    {midCfg : GlobalConfig} {nextProgram : Semantics.Program} {nextDb : Database}
    {txnId : TxnId}
    (hPrefix :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep txnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    (∃ leftMid rightMid leftNext,
      midCfg.program = (.par leftMid rightMid : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨left, db⟩ ⟨leftMid, midCfg.globalDb⟩ ∧
      TxnCommitStep txnId leftMid midCfg.globalDb leftNext nextDb ∧
      nextProgram = (.par leftNext rightMid : Semantics.Program)) ∨
      (∃ leftMid rightMid rightNext,
        midCfg.program = (.par leftMid rightMid : Semantics.Program) ∧
        GlobalMultiStepTR R ⟨right, db⟩ ⟨rightMid, midCfg.globalDb⟩ ∧
        TxnCommitStep txnId rightMid midCfg.globalDb rightNext nextDb ∧
        nextProgram = (.par leftMid rightNext : Semantics.Program)) := by
  rcases commitFreeGlobalMultiStepTR_project_left hPrefix with
    ⟨leftMid, rightMid, hMidProgram, hLeftRun⟩
  rcases commitFreeGlobalMultiStepTR_project_right hPrefix with
    ⟨leftMid', rightMid', hMidProgram', hRightRun⟩
  have hSame :
      (.par leftMid rightMid : Semantics.Program) =
        (.par leftMid' rightMid' : Semantics.Program) := by
    simpa [hMidProgram] using hMidProgram'
  cases hSame
  have hCommit' :
      TxnCommitStep txnId
        (.par leftMid rightMid : Semantics.Program)
        midCfg.globalDb
        nextProgram
        nextDb := by
    simpa [hMidProgram] using hCommit
  rcases txnCommitStep_par_inv hCommit' with hLeftCommit | hRightCommit
  · rcases hLeftCommit with ⟨leftNext, hNextProgram, hLeftCommit⟩
    exact Or.inl ⟨leftMid, rightMid, leftNext, hMidProgram, hLeftRun, hLeftCommit, hNextProgram⟩
  · rcases hRightCommit with ⟨rightNext, hNextProgram, hRightCommit⟩
    exact Or.inr ⟨leftMid, rightMid, rightNext, hMidProgram, hRightRun, hRightCommit, hNextProgram⟩

/-- Server-layer semantic validity. Besides invariant preservation at quiescent states, this records
which state relation every commit step must satisfy. -/
def ParallelValid (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (specs : TxnId → StateSpec) (Ipost : Assertion) : Prop :=
  ∀ db,
    Ipre db →
      (∀ finalCfg,
        GlobalMultiStep R ⟨program, db⟩ finalCfg →
        ProgramDone finalCfg.program →
        Ipost finalCfg.globalDb) ∧
      (∀ midCfg nextProgram nextDb txnId,
        GlobalMultiStep R ⟨program, db⟩ midCfg →
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
        specs txnId midCfg.globalDb nextDb)

def ReachableCommitSpecs (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (specs : TxnId → StateSpec) : Prop :=
  ∀ db,
    Ipre db →
      ∀ midCfg nextProgram nextDb txnId,
        GlobalMultiStep R ⟨program, db⟩ midCfg →
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
        specs txnId midCfg.globalDb nextDb

/-- TR-faithful server validity: quiescent postcondition plus exact commit specifications, but using
the Appendix C interleaving relation. -/
def ParallelValidTR (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (specs : TxnId → StateSpec) (Ipost : Assertion) : Prop :=
  ∀ db,
    Ipre db →
      (∀ finalCfg,
        GlobalMultiStepTR R ⟨program, db⟩ finalCfg →
        ProgramDone finalCfg.program →
        Ipost finalCfg.globalDb) ∧
      (∀ midCfg nextProgram nextDb txnId,
        GlobalMultiStepTR R ⟨program, db⟩ midCfg →
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
        specs txnId midCfg.globalDb nextDb)

def ReachableCommitSpecsTR (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (specs : TxnId → StateSpec) : Prop :=
  ∀ db,
    Ipre db →
      ∀ midCfg nextProgram nextDb txnId,
        GlobalMultiStepTR R ⟨program, db⟩ midCfg →
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
        specs txnId midCfg.globalDb nextDb

def CombinedSpecs (leftSpecs rightSpecs : TxnId → StateSpec) : TxnId → StateSpec :=
  fun txnId db db' => leftSpecs txnId db db' ∨ rightSpecs txnId db db'

/-- A commit specification that is only enabled for one distinguished transaction identifier. This
is the exact server-level shape needed when lifting a proved handler into a parallel composition. -/
def ExactTxnSpec (targetTxnId : TxnId) (spec : StateSpec) : TxnId → StateSpec :=
  fun txnId db db' => txnId = targetTxnId ∧ spec db db'

/-- Compatibility condition saying that `program` can treat every spec in `specs` as allowed
environment interference. This is the current server-level surrogate for a standard RG `par` rule. -/
def ProgramAcceptsSpecs (R : Rely) (specs : TxnId → StateSpec) :
    Semantics.Program → Prop
  | .txn txnId isolation _body =>
      ∀ otherTxn db db' localDb snapshot currentBody,
        specs otherTxn db db' →
        respectsRely R (.txnRuntime txnId isolation localDb snapshot currentBody) db db'
  | .txnRuntime txnId isolation _localDb _snapshot _body =>
      ∀ otherTxn db db' localDb snapshot currentBody,
        specs otherTxn db db' →
        respectsRely R (.txnRuntime txnId isolation localDb snapshot currentBody) db db'
  | .par left right =>
      ProgramAcceptsSpecs R specs left ∧ ProgramAcceptsSpecs R specs right
  | program =>
      ∀ otherTxn db db',
        specs otherTxn db db' →
        respectsRely R program db db'

/-- Mutual version of `ProgramAcceptsSpecs` for two parallel components. -/
def ParallelCompatible (R : Rely)
    (left : Semantics.Program) (leftSpecs : TxnId → StateSpec)
    (right : Semantics.Program) (rightSpecs : TxnId → StateSpec) : Prop :=
  ProgramAcceptsSpecs R rightSpecs left ∧
    ProgramAcceptsSpecs R leftSpecs right

theorem parallelCompatible_symm {R : Rely}
    {left right : Semantics.Program} {leftSpecs rightSpecs : TxnId → StateSpec}
    (h : ParallelCompatible R left leftSpecs right rightSpecs) :
    ParallelCompatible R right rightSpecs left leftSpecs := by
  exact ⟨h.2, h.1⟩

/-- Convenient name for the top-level refinement judgment used by handler proofs. -/
def HandlerRefines (P : Assertion) (R : Rely)
    (program : Semantics.Program) (spec : StateSpec) (Q : Assertion) : Prop :=
  GlobalValid P R program spec Q

/-- TR-faithful variant of `HandlerRefines`, interpreted over `GlobalMultiStepTR`. -/
def HandlerRefinesTR (P : Assertion) (R : Rely)
    (program : Semantics.Program) (spec : StateSpec) (Q : Assertion) : Prop :=
  _root_.DbAppProgramLogic.Logic.GlobalValidTR P R program spec Q

/-- A verified server with relational request specifications. This is the main object to use when a
handler spec is not naturally a pure state transformer. -/
structure VerifiedRequestServerSpec (Req : Type) where
  invariant : Assertion
  rely : Rely
  silent : ∀ db db', rely db db' → db' = db
  requestOf : TxnId → Req
  specs : RequestSpec Req
  program : Semantics.Program
  valid : ParallelValid invariant rely program (RequestSpec.assign requestOf specs) invariant

/-- Same as `VerifiedRequestServerSpec`, but keeps the exact transaction identifier in the internal
specification. This is useful when the external request spec intentionally hides txn ids. -/
structure VerifiedTxnIndexedRequestServerSpec (Req : Type) where
  invariant : Assertion
  rely : Rely
  silent : ∀ db db', rely db db' → db' = db
  requestOf : TxnId → Req
  specs : TxnIndexedRequestSpec Req
  program : Semantics.Program
  valid :
    ParallelValid invariant rely program
      (fun txnId => specs (requestOf txnId) txnId)
      invariant

/-- Server object specialized to pure `state -> state` request transformers. -/
structure VerifiedRequestServer (Req : Type) where
  invariant : Assertion
  rely : Rely
  silent : ∀ db db', rely db db' → db' = db
  requestOf : TxnId → Req
  transformer : RequestTransformer Req
  program : Semantics.Program
  stable : stableAssertion rely invariant
  preserve : ∀ req db, invariant db → invariant (transformer req db)
  valid : ParallelValid invariant rely program (RequestSpec.graphAssign requestOf transformer) invariant

/-- Family of handlers together with relational specs. This is the intended entry point when
modeling an API with one handler per request shape. -/
structure HandlerFamilySpec (Req : Type) where
  invariant : Assertion
  rely : Rely
  handlers : Req → TxnId → Semantics.Program
  specs : RequestSpec Req
  handlerSound :
    ∀ req txnId,
      HandlerRefines invariant rely (handlers req txnId) (specs req) invariant

/-- Transformer-based variant of `HandlerFamilySpec` for state-transformer request specs. -/
structure HandlerFamily (Req : Type) where
  invariant : Assertion
  rely : Rely
  handlers : Req → TxnId → Semantics.Program
  transformer : RequestTransformer Req
  stable : stableAssertion rely invariant
  preserve : ∀ req db, invariant db → invariant (transformer req db)
  handlerSound :
    ∀ req txnId,
      HandlerRefines invariant rely
        (handlers req txnId)
        (StateSpec.graph (transformer req))
        invariant

namespace HandlerFamily

def requestSpecs {Req : Type} (family : HandlerFamily Req) : RequestSpec Req :=
  fun req => StateSpec.graph (family.transformer req)

def toSpec {Req : Type} (family : HandlerFamily Req) : HandlerFamilySpec Req where
  invariant := family.invariant
  rely := family.rely
  handlers := family.handlers
  specs := family.requestSpecs
  handlerSound := family.handlerSound

end HandlerFamily

theorem reachableInvariant_of_reachableCommitSpecs {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db db', I db → specs txnId db db' → I db')
    (hCommits : ReachableCommitSpecs I R program specs)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : I db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    I finalCfg.globalDb := by
  induction hRun with
  | refl =>
      simpa using hDb
  | tail hPrev hLast ih =>
      cases hLast with
      | inl hActual =>
          rcases step_sameDb_or_commit hActual with hEq | hCommit
          · simpa [hEq] using ih
          · rcases hCommit with ⟨txnId, hCommit⟩
            exact hPreserve txnId _ _ ih (hCommits db hDb _ _ _ _ hPrev hCommit)
      | inr hRely =>
          rcases hRely with ⟨_hProgram, hRespect⟩
          exact hStable _ _ ih (respectsRely_implies hRespect)

theorem parallelValid_of_reachableCommitSpecs {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db db', I db → specs txnId db db' → I db')
    (hCommits : ReachableCommitSpecs I R program specs) :
    ParallelValid I R program specs I := by
  intro db hDb
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun _hDone
    exact reachableInvariant_of_reachableCommitSpecs hStable hPreserve hCommits hDb hRun
  · intro midCfg nextProgram nextDb txnId hRun hCommit
    exact hCommits db hDb midCfg nextProgram nextDb txnId hRun hCommit

theorem reachableInvariant_of_reachableCommitSpecsTR {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db db', I db → specs txnId db db' → I db')
    (hCommits : ReachableCommitSpecsTR I R program specs)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : I db)
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg) :
    I finalCfg.globalDb := by
  induction hRun with
  | refl =>
      simpa using hDb
  | tail hPrev hLast ih =>
      cases hLast with
      | inl hActual =>
          rcases step_sameDb_or_commit hActual with hEq | hCommit
          · simpa [hEq] using ih
          · rcases hCommit with ⟨txnId, hCommit⟩
            exact hPreserve txnId _ _ ih (hCommits db hDb _ _ _ _ hPrev hCommit)
      | inr hRely =>
          rcases hRely with ⟨_hProgram, hR⟩
          exact hStable _ _ ih hR

theorem parallelValidTR_of_reachableCommitSpecs {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db db', I db → specs txnId db db' → I db')
    (hCommits : ReachableCommitSpecsTR I R program specs) :
    ParallelValidTR I R program specs I := by
  intro db hDb
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun _hDone
    exact reachableInvariant_of_reachableCommitSpecsTR hStable hPreserve hCommits hDb hRun
  · intro midCfg nextProgram nextDb txnId hRun hCommit
    exact hCommits db hDb midCfg nextProgram nextDb txnId hRun hCommit

theorem programAcceptsSpecs_respectsRely {R : Rely} {specs : TxnId → StateSpec}
    {program : Semantics.Program}
    (hAccept : ProgramAcceptsSpecs R specs program)
    {txnId : TxnId} {db db' : Database}
    (hSpec : specs txnId db db') :
    respectsRely R program db db' := by
  cases program with
  | txn txnId0 isolation body =>
      have hRuntime :
          respectsRely R
            (.txnRuntime txnId0 isolation [] db (Command.skip : Semantics.Program))
            db
            db' := by
        exact hAccept txnId db db' [] db (Command.skip : Semantics.Program) hSpec
      have hPair : R db db' ∧ isolation.commit [] db db' := by
        simpa [respectsRely] using hRuntime
      simpa [respectsRely] using hPair.1
  | txnRuntime txnId0 isolation localDb snapshot body =>
      exact hAccept txnId db db' localDb snapshot body hSpec
  | par left right =>
      rcases hAccept with ⟨hLeft, hRight⟩
      exact ⟨programAcceptsSpecs_respectsRely hLeft hSpec,
        programAcceptsSpecs_respectsRely hRight hSpec⟩
  | skip =>
      exact hAccept txnId db db' hSpec
  | letE x expr body =>
      exact hAccept txnId db db' hSpec
  | ite cond thenBranch elseBranch =>
      exact hAccept txnId db db' hSpec
  | seq left right =>
      exact hAccept txnId db db' hSpec
  | insert expr =>
      exact hAccept txnId db db' hSpec
  | delete source predicate =>
      exact hAccept txnId db db' hSpec
  | select binder source predicate body =>
      exact hAccept txnId db db' hSpec
  | update source updateExpr predicate =>
      exact hAccept txnId db db' hSpec
  | foreach source doneVar elemVar body =>
      exact hAccept txnId db db' hSpec
  | foreachRuntime done remaining doneVar elemVar body =>
      exact hAccept txnId db db' hSpec

theorem refreshVisible_preserves_acceptsSpecs {R : Rely} {specs : TxnId → StateSpec}
    {program : Semantics.Program} {db : Database}
    (hAccept : ProgramAcceptsSpecs R specs program) :
    ProgramAcceptsSpecs R specs (refreshVisible program db) := by
  cases program with
  | txnRuntime txnId isolation localDb snapshot body =>
      simpa [refreshVisible, ProgramAcceptsSpecs] using hAccept
  | par left right =>
      exact ⟨refreshVisible_preserves_acceptsSpecs hAccept.1,
        refreshVisible_preserves_acceptsSpecs hAccept.2⟩
  | _ =>
      simpa [refreshVisible] using hAccept

theorem step_preserves_acceptsSpecs {R : Rely} {specs : TxnId → StateSpec}
    {program program' : Semantics.Program} {db db' : Database}
    (hStep : Semantics.Step program db program' db')
    (hAccept : ProgramAcceptsSpecs R specs program) :
    ProgramAcceptsSpecs R specs program' := by
  induction hStep with
  | txnStart =>
      simpa [ProgramAcceptsSpecs] using hAccept
  | txnExec =>
      simpa [ProgramAcceptsSpecs] using hAccept
  | txnCommit =>
      intro otherTxn db₀ db₁ hSpec
      have hBase : R db₀ db₁ := by
        exact respectsRely_implies (programAcceptsSpecs_respectsRely hAccept hSpec)
      simpa [ProgramAcceptsSpecs, respectsRely] using hBase
  | parLeft hInner ih =>
      rcases hAccept with ⟨hLeft, hRight⟩
      exact ⟨ih hLeft, hRight⟩
  | parRight hInner ih =>
      rcases hAccept with ⟨hLeft, hRight⟩
      exact ⟨hLeft, ih hRight⟩

theorem globalInterleavedStep_preserves_acceptsSpecs {R : Rely} {specs : TxnId → StateSpec}
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg')
    (hAccept : ProgramAcceptsSpecs R specs cfg.program) :
    ProgramAcceptsSpecs R specs cfg'.program := by
  cases hStep with
  | inl hActual =>
      exact step_preserves_acceptsSpecs hActual hAccept
  | inr hRely =>
      rcases hRely with ⟨hProgram, _hRespect⟩
      rw [hProgram]
      exact refreshVisible_preserves_acceptsSpecs hAccept

theorem globalMultiStep_preserves_acceptsSpecs {R : Rely} {specs : TxnId → StateSpec}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂)
    (hAccept : ProgramAcceptsSpecs R specs cfg₁.program) :
    ProgramAcceptsSpecs R specs cfg₂.program := by
  induction hRun with
  | refl =>
      exact hAccept
  | tail hPrev hLast ih =>
      exact globalInterleavedStep_preserves_acceptsSpecs hLast ih

theorem refreshVisible_preserves_nonParallel
    {program : Semantics.Program} {db : Database}
    (h : NonParallel program) :
    NonParallel (refreshVisible program db) := by
  cases program <;> simp [NonParallel, refreshVisible] at h ⊢

theorem step_preserves_nonParallel
    {program program' : Semantics.Program} {db db' : Database}
    (hStep : Semantics.Step program db program' db')
    (h : NonParallel program) :
    NonParallel program' := by
  induction hStep with
  | txnStart =>
      simp [NonParallel]
  | txnExec =>
      simp [NonParallel]
  | txnCommit =>
      simp [NonParallel]
  | parLeft =>
      cases h
  | parRight =>
      cases h

theorem globalInterleavedStep_preserves_nonParallel {R : Rely}
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg')
    (h : NonParallel cfg.program) :
    NonParallel cfg'.program := by
  cases hStep with
  | inl hActual =>
      exact step_preserves_nonParallel hActual h
  | inr hRely =>
      rcases hRely with ⟨hProgram, _hRespect⟩
      rw [hProgram]
      exact refreshVisible_preserves_nonParallel h

theorem globalMultiStep_preserves_nonParallel {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂)
    (h : NonParallel cfg₁.program) :
    NonParallel cfg₂.program := by
  induction hRun with
  | refl =>
      exact h
  | tail hPrev hLast ih =>
      exact globalInterleavedStep_preserves_nonParallel hLast ih

theorem refreshVisible_preserves_singleTxn {txnId : TxnId}
    {program : Semantics.Program} {db : Database}
    (h : SingleTxnProgram txnId program) :
    SingleTxnProgram txnId (refreshVisible program db) := by
  cases h with
  | txn =>
      simp [refreshVisible]
      exact SingleTxnProgram.txn
  | runtime =>
      simp [refreshVisible]
      exact SingleTxnProgram.runtime
  | skip =>
      simp [refreshVisible]
      exact SingleTxnProgram.skip

theorem step_preserves_singleTxn {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hStep : Semantics.Step program db program' db')
    (h : SingleTxnProgram txnId program) :
    SingleTxnProgram txnId program' := by
  induction hStep with
  | txnStart =>
      cases h with
      | txn =>
          exact SingleTxnProgram.runtime
  | txnExec =>
      cases h with
      | runtime =>
          exact SingleTxnProgram.runtime
  | txnCommit =>
      cases h with
      | runtime =>
          exact SingleTxnProgram.skip
  | parLeft =>
      cases h
  | parRight =>
      cases h

theorem globalInterleavedStep_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg')
    (h : SingleTxnProgram txnId cfg.program) :
    SingleTxnProgram txnId cfg'.program := by
  cases hStep with
  | inl hActual =>
      exact step_preserves_singleTxn hActual h
  | inr hRely =>
      rcases hRely with ⟨hProgram, _hRespect⟩
      rw [hProgram]
      exact refreshVisible_preserves_singleTxn h

theorem globalMultiStep_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂)
    (h : SingleTxnProgram txnId cfg₁.program) :
    SingleTxnProgram txnId cfg₂.program := by
  induction hRun with
  | refl =>
      exact h
  | tail hPrev hLast ih =>
      exact globalInterleavedStep_preserves_singleTxn hLast ih

theorem globalInterleavedStepTR_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStepTR R cfg cfg')
    (h : SingleTxnProgram txnId cfg.program) :
    SingleTxnProgram txnId cfg'.program := by
  cases hStep with
  | inl hActual =>
      exact step_preserves_singleTxn hActual h
  | inr hRely =>
      rcases hRely with ⟨hProgram, _hR⟩
      rw [hProgram]
      exact h

theorem globalMultiStepTR_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStepTR R cfg₁ cfg₂)
    (h : SingleTxnProgram txnId cfg₁.program) :
    SingleTxnProgram txnId cfg₂.program := by
  induction hRun with
  | refl =>
      exact h
  | tail hPrev hLast ih =>
      exact globalInterleavedStepTR_preserves_singleTxn hLast ih

theorem globalMultiStepTR_append_rely {R : Rely}
    {program₀ program : Semantics.Program} {db₀ db db' : Database}
    (hRun : GlobalMultiStepTR R ⟨program₀, db₀⟩ ⟨program, db⟩)
    (hR : R db db') :
    GlobalMultiStepTR R ⟨program₀, db₀⟩ ⟨program, db'⟩ := by
  exact MultiStep.tail hRun (Or.inr ⟨rfl, hR⟩)

theorem step_not_skip_of_singleTxn_noCommit {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hSingle : SingleTxnProgram txnId program)
    (hStep : Semantics.Step program db program' db')
    (hNoCommit : ¬ ∃ otherTxnId, TxnCommitStep otherTxnId program db program' db') :
    program' ≠ (Command.skip : Semantics.Program) := by
  cases hStep with
  | txnStart =>
      simp
  | txnExec =>
      simp
  | txnCommit hCommit =>
      intro _hEq
      exact hNoCommit ⟨_, TxnCommitStep.root hCommit⟩
  | parLeft =>
      cases hSingle
  | parRight =>
      cases hSingle

theorem commitFreeGlobalMultiStepTR_singleTxn_notSkip {txnId : TxnId} {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : CommitFreeGlobalMultiStepTR R cfg₁ cfg₂)
    (hSingle : SingleTxnProgram txnId cfg₁.program) :
    cfg₁.program ≠ (Command.skip : Semantics.Program) →
    cfg₂.program ≠ (Command.skip : Semantics.Program) := by
  intro hNotStartSkip
  revert hSingle
  induction hRun with
  | refl =>
      cases cfg₁ with
      | mk program db =>
          intro hSingle
          cases hSingle with
          | txn =>
              simp
          | runtime =>
              simp
          | skip =>
              exact False.elim (hNotStartSkip rfl)
  | tail hPrev hStep hNoCommit ih =>
      intro hSingle
      have hSingleMid := globalMultiStepTR_preserves_singleTxn hPrev.toMultiStep hSingle
      cases hStep with
      | inl hActual =>
          exact step_not_skip_of_singleTxn_noCommit hSingleMid hActual hNoCommit
      | inr hRely =>
          rcases hRely with ⟨hProgram, _hR⟩
          rw [hProgram]
          exact ih hSingle

theorem commitFreeGlobalMultiStepTR_par_notDone_of_leftTxn {R : Rely}
    {txnId : TxnId} {left right : Semantics.Program}
    {db : Database} {finalCfg : GlobalConfig}
    (hLeft : SingleTxnProgram txnId left)
    (hLeftNotSkip : left ≠ (Command.skip : Semantics.Program))
    (hRun :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par left right : Semantics.Program), db⟩
        finalCfg) :
    ¬ ProgramDone finalCfg.program := by
  intro hDone
  rcases commitFreeGlobalMultiStepTR_project_left_commitFree hRun with
    ⟨leftFinal, rightFinal, hProgram, hLeftRun⟩
  have hDoneLeft : ProgramDone leftFinal := by
    rw [hProgram] at hDone
    cases hDone with
    | par hLeftDone _hRightDone =>
        exact hLeftDone
  have hSingleFinal : SingleTxnProgram txnId leftFinal := by
    exact globalMultiStepTR_preserves_singleTxn hLeftRun.toMultiStep hLeft
  cases hDoneLeft with
  | skip =>
      exact commitFreeGlobalMultiStepTR_singleTxn_notSkip hLeftRun hLeft hLeftNotSkip rfl
  | par hLeftDone _hRightDone =>
      cases singleTxn_nonParallel hSingleFinal

theorem txnCommitStep_txnId_eq_of_singleTxn {expectedTxnId actualTxnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hSingle : SingleTxnProgram expectedTxnId program)
    (hCommit : TxnCommitStep actualTxnId program db program' db') :
    actualTxnId = expectedTxnId := by
  cases hCommit with
  | root =>
      cases hSingle with
      | runtime =>
          rfl
  | parLeft =>
      cases hSingle
  | parRight =>
      cases hSingle

theorem programDone_eq_skip_of_nonParallel
    {program : Semantics.Program}
    (hDone : ProgramDone program)
    (h : NonParallel program) :
    program = (Command.skip : Semantics.Program) := by
  cases hDone with
  | skip =>
      rfl
  | par hLeft hRight =>
      cases h

theorem txnCommitStep_of_nonParallel {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (h : NonParallel program)
    (hCommit : TxnCommitStep txnId program db program' db') :
    ∃ isolation localDb snapshot,
      program =
        (.txnRuntime txnId isolation localDb snapshot (Command.skip : Semantics.Program)) ∧
      program' = (Command.skip : Semantics.Program) ∧
      db' = Database.flush localDb db ∧
      isolation.commit localDb snapshot db := by
  cases hCommit with
  | root hCommitGuard =>
      exact ⟨_, _, _, rfl, rfl, rfl, hCommitGuard⟩
  | parLeft hInner =>
      cases h
  | parRight hInner =>
      cases h

/-- Any commit reached in a standalone run of a single transaction satisfies the handler-level state
specification proved for that transaction. This packages the repeated "reachable runtime state +
commit step" argument used throughout the server layer. -/
theorem txnCommitSpec_of_handlerRefines {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost)
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database} {actualTxnId : TxnId}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨(.txn txnId isolation body : Semantics.Program), db⟩ midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnId ∧ spec midCfg.globalDb nextDb := by
  have hSingle : SingleTxnProgram txnId midCfg.program := by
    exact globalMultiStep_preserves_singleTxn hRun SingleTxnProgram.txn
  have hTxnIdEq : actualTxnId = txnId := by
    exact txnCommitStep_txnId_eq_of_singleTxn hSingle hCommit
  have hNonPar : NonParallel midCfg.program := by
    exact singleTxn_nonParallel hSingle
  rcases txnCommitStep_of_nonParallel hNonPar hCommit with
    ⟨_, _, _, hProgram, hNextSkip, hDbEq, hCommitGuard⟩
  have hStep : Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb := by
    rw [hProgram, hNextSkip, hDbEq]
    exact Semantics.Step.txnCommit hCommitGuard
  subst hTxnIdEq
  rcases h db hDb with ⟨_hPost, hTxnGuaranteed⟩
  exact ⟨rfl, hTxnGuaranteed midCfg nextProgram nextDb hRun hStep hNextSkip⟩

theorem txnCommitSpec_of_handlerRefinesTR {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefinesTR Ipre R (.txn txnId isolation body) spec Ipost)
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database} {actualTxnId : TxnId}
    (hDb : Ipre db)
    (hRun : GlobalMultiStepTR R ⟨(.txn txnId isolation body : Semantics.Program), db⟩ midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnId ∧ spec midCfg.globalDb nextDb := by
  have hSingle : SingleTxnProgram txnId midCfg.program := by
    exact globalMultiStepTR_preserves_singleTxn hRun SingleTxnProgram.txn
  have hTxnIdEq : actualTxnId = txnId := by
    exact txnCommitStep_txnId_eq_of_singleTxn hSingle hCommit
  have hNonPar : NonParallel midCfg.program := by
    exact singleTxn_nonParallel hSingle
  rcases txnCommitStep_of_nonParallel hNonPar hCommit with
    ⟨_, _, _, hProgram, hNextSkip, hDbEq, hCommitGuard⟩
  have hStep : Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb := by
    rw [hProgram, hNextSkip, hDbEq]
    exact Semantics.Step.txnCommit hCommitGuard
  subst hTxnIdEq
  rcases h db hDb with ⟨_hPost, hTxnGuaranteed⟩
  exact ⟨rfl, hTxnGuaranteed midCfg nextProgram nextDb hRun hStep hNextSkip⟩

theorem programDone_par_skip_right_inv {program : Semantics.Program}
    (hDone : ProgramDone (.par program (Command.skip : Semantics.Program))) :
    ProgramDone program := by
  cases hDone with
  | par hLeft hRight =>
      exact hLeft

theorem programDone_par_skip_left_inv {program : Semantics.Program}
    (hDone : ProgramDone (.par (Command.skip : Semantics.Program) program)) :
    ProgramDone program := by
  cases hDone with
  | par hLeft hRight =>
      exact hRight

theorem txnCommitStep_par_skip_right {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hCommit :
      TxnCommitStep txnId (.par program (Command.skip : Semantics.Program)) db program' db') :
    ∃ programInner,
      program' = (.par programInner (Command.skip : Semantics.Program) : Semantics.Program) ∧
      TxnCommitStep txnId program db programInner db' := by
  cases hCommit with
  | parLeft hInner =>
      exact ⟨_, rfl, hInner⟩
  | parRight hInner =>
      cases hInner

theorem txnCommitStep_par_skip_left {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hCommit :
      TxnCommitStep txnId (.par (Command.skip : Semantics.Program) program) db program' db') :
    ∃ programInner,
      program' = (.par (Command.skip : Semantics.Program) programInner : Semantics.Program) ∧
      TxnCommitStep txnId program db programInner db' := by
  cases hCommit with
  | parLeft hInner =>
      cases hInner
  | parRight hInner =>
      exact ⟨_, rfl, hInner⟩

theorem globalInterleavedStep_par_skip_right {R : Rely}
    {program program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStep R
        ⟨(.par program (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        ⟨program', db'⟩) :
    ∃ programInner,
      program' = (.par programInner (Command.skip : Semantics.Program) : Semantics.Program) ∧
      globalInterleavedStep R ⟨program, db⟩ ⟨programInner, db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          exact ⟨_, rfl, Or.inl hInner⟩
      | parRight hInner =>
          cases no_step_from_program_skip hInner
  | inr hRely =>
      rcases hRely with ⟨hProgram, hRespect⟩
      refine ⟨refreshVisible program db', ?_, ?_⟩
      · simpa [refreshVisible] using hProgram
      · exact Or.inr ⟨rfl, by simpa [respectsRely] using hRespect.1⟩

theorem globalInterleavedStep_par_skip_left {R : Rely}
    {program program' : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStep R
        ⟨(.par (Command.skip : Semantics.Program) program : Semantics.Program), db⟩
        ⟨program', db'⟩) :
    ∃ programInner,
      program' = (.par (Command.skip : Semantics.Program) programInner : Semantics.Program) ∧
      globalInterleavedStep R ⟨program, db⟩ ⟨programInner, db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases no_step_from_program_skip hInner
      | parRight hInner =>
          exact ⟨_, rfl, Or.inl hInner⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hRespect⟩
      refine ⟨refreshVisible program db', ?_, ?_⟩
      · simpa [refreshVisible] using hProgram
      · exact Or.inr ⟨rfl, by simpa [respectsRely] using hRespect.2⟩

theorem globalMultiStep_par_skip_right {R : Rely}
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      GlobalMultiStep R
        ⟨(.par program (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        finalCfg) :
    ∃ programInner,
      finalCfg.program = (.par programInner (Command.skip : Semantics.Program) : Semantics.Program) ∧
      GlobalMultiStep R ⟨program, db⟩ ⟨programInner, finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨program, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgramActual midDb =>
          rcases ih with ⟨midProgram, hMidEq, hPrev'⟩
          cases hMidEq
          rcases globalInterleavedStep_par_skip_right hLast with ⟨midProgram', hLastEq, hLast'⟩
          exact ⟨midProgram', hLastEq, MultiStep.tail hPrev' hLast'⟩

theorem globalMultiStep_par_skip_left {R : Rely}
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      GlobalMultiStep R
        ⟨(.par (Command.skip : Semantics.Program) program : Semantics.Program), db⟩
        finalCfg) :
    ∃ programInner,
      finalCfg.program = (.par (Command.skip : Semantics.Program) programInner : Semantics.Program) ∧
      GlobalMultiStep R ⟨program, db⟩ ⟨programInner, finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨program, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgramActual midDb =>
          rcases ih with ⟨midProgram, hMidEq, hPrev'⟩
          cases hMidEq
          rcases globalInterleavedStep_par_skip_left hLast with ⟨midProgram', hLastEq, hLast'⟩
          exact ⟨midProgram', hLastEq, MultiStep.tail hPrev' hLast'⟩

theorem globalInterleavedStepTR_par_skip_right {R : Rely}
    {program programInner : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par program (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        ⟨programInner, db'⟩) :
    ∃ programInner',
      programInner = (.par programInner' (Command.skip : Semantics.Program) : Semantics.Program) ∧
      globalInterleavedStepTR R ⟨program, db⟩ ⟨programInner', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          exact ⟨_, rfl, Or.inl hInner⟩
      | parRight hInner =>
          cases no_step_from_program_skip hInner
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨program, ?_, ?_⟩
      · simpa using hProgram
      · exact Or.inr ⟨rfl, hR⟩

theorem globalInterleavedStepTR_par_skip_left {R : Rely}
    {program programInner : Semantics.Program} {db db' : Database}
    (hStep :
      globalInterleavedStepTR R
        ⟨(.par (Command.skip : Semantics.Program) program : Semantics.Program), db⟩
        ⟨programInner, db'⟩) :
    ∃ programInner',
      programInner = (.par (Command.skip : Semantics.Program) programInner' : Semantics.Program) ∧
      globalInterleavedStepTR R ⟨program, db⟩ ⟨programInner', db'⟩ := by
  cases hStep with
  | inl hActual =>
      cases hActual with
      | parLeft hInner =>
          cases no_step_from_program_skip hInner
      | parRight hInner =>
          exact ⟨_, rfl, Or.inl hInner⟩
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      refine ⟨program, ?_, ?_⟩
      · simpa using hProgram
      · exact Or.inr ⟨rfl, hR⟩

theorem globalMultiStepTR_par_skip_right {R : Rely}
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      GlobalMultiStepTR R
        ⟨(.par program (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        finalCfg) :
    ∃ programInner,
      finalCfg.program = (.par programInner (Command.skip : Semantics.Program) : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨program, db⟩ ⟨programInner, finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨program, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgramActual midDb =>
          rcases ih with ⟨midProgram, hMidEq, hPrev'⟩
          cases hMidEq
          rcases globalInterleavedStepTR_par_skip_right hLast with ⟨midProgram', hLastEq, hLast'⟩
          exact ⟨midProgram', hLastEq, MultiStep.tail hPrev' hLast'⟩

theorem globalMultiStepTR_par_skip_left {R : Rely}
    {program : Semantics.Program} {db : Database} {finalCfg : GlobalConfig}
    (hRun :
      GlobalMultiStepTR R
        ⟨(.par (Command.skip : Semantics.Program) program : Semantics.Program), db⟩
        finalCfg) :
    ∃ programInner,
      finalCfg.program = (.par (Command.skip : Semantics.Program) programInner : Semantics.Program) ∧
      GlobalMultiStepTR R ⟨program, db⟩ ⟨programInner, finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨program, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfgMid cfgFinal
      cases cfgMid with
      | mk midProgramActual midDb =>
          rcases ih with ⟨midProgram, hMidEq, hPrev'⟩
          cases hMidEq
          rcases globalInterleavedStepTR_par_skip_left hLast with ⟨midProgram', hLastEq, hLast'⟩
          exact ⟨midProgram', hLastEq, MultiStep.tail hPrev' hLast'⟩

theorem ParallelValid.invariant {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (h : ParallelValid I R program specs I)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : I db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg)
    (hDone : ProgramDone finalCfg.program) :
    I finalCfg.globalDb := by
  exact (h db hDb).1 finalCfg hRun hDone

theorem ParallelValid.commitSpec {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost)
    {db : Database} (hDb : Ipre db)
    {midCfg : GlobalConfig} {nextProgram : Semantics.Program} {nextDb : Database}
    {txnId : TxnId}
    (hRun : GlobalMultiStep R ⟨program, db⟩ midCfg)
    (hCommit : TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb) :
    specs txnId midCfg.globalDb nextDb := by
  exact (h db hDb).2 midCfg nextProgram nextDb txnId hRun hCommit

theorem parallelValid_mono {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs specs' : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost)
    (hImp : ∀ txnId db db', specs txnId db db' → specs' txnId db db') :
    ParallelValid Ipre R program specs' Ipost := by
  intro db hDb
  rcases h db hDb with ⟨hPost, hCommit⟩
  refine ⟨hPost, ?_⟩
  intro midCfg nextProgram nextDb txnId hRun hStep
  exact hImp txnId _ _ (hCommit _ _ _ _ hRun hStep)

theorem parallelValid_hideTxnIds {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {Req : Type}
    {requestOf : TxnId → Req} {specs : TxnIndexedRequestSpec Req} {Ipost : Assertion}
    (h :
      ParallelValid Ipre R program
        (fun txnId => specs (requestOf txnId) txnId)
        Ipost) :
    ParallelValid Ipre R program
      (RequestSpec.assign requestOf (RequestSpec.hideTxnIds requestOf specs))
      Ipost := by
  refine parallelValid_mono h ?_
  intro txnId db db' hSpec
  exact ⟨txnId, rfl, hSpec⟩

theorem ParallelValid.reachableCommitSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost) :
    ReachableCommitSpecs Ipre R program specs := by
  intro db hDb midCfg nextProgram nextDb txnId hRun hCommit
  exact ParallelValid.commitSpec h hDb hRun hCommit

theorem ParallelValidTR.invariant {I : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec}
    (h : ParallelValidTR I R program specs I)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : I db)
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg)
    (hDone : ProgramDone finalCfg.program) :
    I finalCfg.globalDb := by
  exact (h db hDb).1 finalCfg hRun hDone

theorem ParallelValidTR.commitSpec {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValidTR Ipre R program specs Ipost)
    {db : Database} (hDb : Ipre db)
    {midCfg : GlobalConfig} {nextProgram : Semantics.Program} {nextDb : Database}
    {txnId : TxnId}
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ midCfg)
    (hCommit : TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb) :
    specs txnId midCfg.globalDb nextDb := by
  exact (h db hDb).2 midCfg nextProgram nextDb txnId hRun hCommit

theorem ParallelValidTR.reachableCommitSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValidTR Ipre R program specs Ipost) :
    ReachableCommitSpecsTR Ipre R program specs := by
  intro db hDb midCfg nextProgram nextDb txnId hRun hCommit
  exact ParallelValidTR.commitSpec h hDb hRun hCommit

theorem parallelValidTR_commitSequence {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValidTR Ipre R program specs Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg) :
    ∃ commits, CommitSequence specs db commits finalCfg.globalDb := by
  induction hRun with
  | refl =>
      exact ⟨[], CommitSequence.nil⟩
  | tail hPrev hLast ih =>
      rcases ih with ⟨commits, hSeq⟩
      cases globalInterleavedStepTR_sameDb_or_commit hSilent hLast with
      | inl hEq =>
          refine ⟨commits, ?_⟩
          simpa [hEq] using hSeq
      | inr hCommit =>
          rcases hCommit with ⟨txnId, hCommit⟩
          refine ⟨commits ++ [txnId], ?_⟩
          exact CommitSequence.snoc hSeq (ParallelValidTR.commitSpec hValid hDb hPrev hCommit)

theorem parallelValidTR_commitLog {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValidTR Ipre R program specs Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg) :
    ∃ events, CommitLog specs db events finalCfg.globalDb := by
  rcases parallelValidTR_commitSequence hSilent hValid hDb hRun with ⟨commits, hSeq⟩
  exact CommitLog.ofCommitSequence hSeq

theorem parallelValidTR_eventFoldl_of_graphSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {fs : TxnId → StateTransformer} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValidTR Ipre R program (fun txnId => StateSpec.graph (fs txnId)) Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStepTR R ⟨program, db⟩ finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl (fun current (event : CommitEvent) => fs event.txnId current) db events := by
  rcases parallelValidTR_commitLog hSilent hValid hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.graph_implies_foldl hLog⟩

theorem parallelValid_commitSequence {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid Ipre R program specs Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    ∃ commits, CommitSequence specs db commits finalCfg.globalDb := by
  induction hRun with
  | refl =>
      exact ⟨[], CommitSequence.nil⟩
  | tail hPrev hLast ih =>
      rcases ih with ⟨commits, hSeq⟩
      cases globalInterleavedStep_sameDb_or_commit hSilent hLast with
      | inl hEq =>
          refine ⟨commits, ?_⟩
          simpa [hEq] using hSeq
      | inr hCommit =>
          rcases hCommit with ⟨txnId, hCommit⟩
          refine ⟨commits ++ [txnId], ?_⟩
          exact CommitSequence.snoc hSeq (ParallelValid.commitSpec hValid hDb hPrev hCommit)

theorem parallelValid_commitLog {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid Ipre R program specs Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    ∃ events, CommitLog specs db events finalCfg.globalDb := by
  rcases parallelValid_commitSequence hSilent hValid hDb hRun with ⟨commits, hSeq⟩
  exact CommitLog.ofCommitSequence hSeq

theorem parallelValid_foldl_of_graphSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {fs : TxnId → StateTransformer} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid Ipre R program (fun txnId => StateSpec.graph (fs txnId)) Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    ∃ commits, finalCfg.globalDb = List.foldl (fun current txnId => fs txnId current) db commits := by
  rcases parallelValid_commitSequence hSilent hValid hDb hRun with ⟨commits, hSeq⟩
  refine ⟨commits, (CommitSequence.graph_iff_foldl.mp hSeq)⟩

theorem parallelValid_eventFoldl_of_graphSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {fs : TxnId → StateTransformer} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid Ipre R program (fun txnId => StateSpec.graph (fs txnId)) Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl (fun current (event : CommitEvent) => fs event.txnId current) db events := by
  rcases parallelValid_commitLog hSilent hValid hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.graph_implies_foldl hLog⟩

theorem parallelValid_eventFoldl_of_requestGraphSpecs
    {Req : Type} {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {requestOf : TxnId → Req}
    {fs : RequestTransformer Req} {Ipost : Assertion}
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid Ipre R program (RequestSpec.graphAssign requestOf fs) Ipost)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : Ipre db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl (fun current req => fs req current) db (CommitLog.requests requestOf events) := by
  rcases parallelValid_commitLog hSilent hValid hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.graphAssign_implies_foldl_requests hLog⟩

theorem eventFoldl_of_reachableGraphSpecs {I : Assertion} {R : Rely}
    {program : Semantics.Program} {fs : TxnId → StateTransformer}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db, I db → I (fs txnId db))
    (hSilent : ∀ db db', R db db' → db' = db)
    (hCommits :
      ReachableCommitSpecs I R program (fun txnId => StateSpec.graph (fs txnId))) :
    ∀ {db : Database} {finalCfg : GlobalConfig},
      I db →
      GlobalMultiStep R ⟨program, db⟩ finalCfg →
      ∃ events,
        finalCfg.globalDb =
          List.foldl (fun current (event : CommitEvent) => fs event.txnId current) db events := by
  intro db finalCfg hDb hRun
  have hValid :
      ParallelValid I R program (fun txnId => StateSpec.graph (fs txnId)) I := by
    refine parallelValid_of_reachableCommitSpecs hStable ?_ hCommits
    intro txnId db db' hI hSpec
    rcases hSpec with rfl
    exact hPreserve txnId db hI
  exact parallelValid_eventFoldl_of_graphSpecs hSilent hValid hDb hRun

theorem reachableGraphSpecs_sound {I : Assertion} {R : Rely}
    {program : Semantics.Program} {fs : TxnId → StateTransformer}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ txnId db, I db → I (fs txnId db))
    (hSilent : ∀ db db', R db db' → db' = db)
    (hCommits :
      ReachableCommitSpecs I R program (fun txnId => StateSpec.graph (fs txnId))) :
    ∀ {db : Database} {finalCfg : GlobalConfig},
      I db →
      GlobalMultiStep R ⟨program, db⟩ finalCfg →
      I finalCfg.globalDb ∧
        ∃ events,
          finalCfg.globalDb =
            List.foldl (fun current (event : CommitEvent) => fs event.txnId current) db events := by
  intro db finalCfg hDb hRun
  refine ⟨?_, ?_⟩
  · exact reachableInvariant_of_reachableCommitSpecs hStable
      (by
        intro txnId db db' hI hSpec
        rcases hSpec with rfl
        exact hPreserve txnId db hI)
      hCommits
      hDb
      hRun
  · exact eventFoldl_of_reachableGraphSpecs hStable hPreserve hSilent hCommits hDb hRun

theorem eventFoldl_of_reachableRequestGraphSpecs {Req : Type} {I : Assertion} {R : Rely}
    {program : Semantics.Program} {requestOf : TxnId → Req} {fs : RequestTransformer Req}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ req db, I db → I (fs req db))
    (hSilent : ∀ db db', R db db' → db' = db)
    (hCommits :
      ReachableCommitSpecs I R program (RequestSpec.graphAssign requestOf fs)) :
    ∀ {db : Database} {finalCfg : GlobalConfig},
      I db →
      GlobalMultiStep R ⟨program, db⟩ finalCfg →
      ∃ events,
        finalCfg.globalDb =
          List.foldl (fun current req => fs req current) db (CommitLog.requests requestOf events) := by
  intro db finalCfg hDb hRun
  rcases parallelValid_commitLog hSilent
      (parallelValid_of_reachableCommitSpecs hStable
        (by
          intro txnId db db' hI hSpec
          rcases hSpec with rfl
          exact hPreserve (requestOf txnId) db hI)
        hCommits)
      hDb
      hRun with
    ⟨events, hLog⟩
  exact ⟨events, CommitLog.graphAssign_implies_foldl_requests hLog⟩

theorem reachableRequestGraphSpecs_sound {Req : Type} {I : Assertion} {R : Rely}
    {program : Semantics.Program} {requestOf : TxnId → Req} {fs : RequestTransformer Req}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ req db, I db → I (fs req db))
    (hSilent : ∀ db db', R db db' → db' = db)
    (hCommits :
      ReachableCommitSpecs I R program (RequestSpec.graphAssign requestOf fs)) :
    ∀ {db : Database} {finalCfg : GlobalConfig},
      I db →
      GlobalMultiStep R ⟨program, db⟩ finalCfg →
      I finalCfg.globalDb ∧
        ∃ events,
          finalCfg.globalDb =
            List.foldl (fun current req => fs req current) db (CommitLog.requests requestOf events) := by
  intro db finalCfg hDb hRun
  refine ⟨?_, ?_⟩
  · exact reachableInvariant_of_reachableCommitSpecs hStable
      (by
        intro txnId db db' hI hSpec
        rcases hSpec with rfl
        exact hPreserve (requestOf txnId) db hI)
      hCommits
      hDb
      hRun
  · exact eventFoldl_of_reachableRequestGraphSpecs hStable hPreserve hSilent hCommits hDb hRun

theorem parallelValid_requestGraphSpecs_sound
    {Req : Type} {I : Assertion} {R : Rely}
    {program : Semantics.Program} {requestOf : TxnId → Req}
    {fs : RequestTransformer Req}
    (hStable : stableAssertion R I)
    (hPreserve : ∀ req db, I db → I (fs req db))
    (hSilent : ∀ db db', R db db' → db' = db)
    (hValid : ParallelValid I R program (RequestSpec.graphAssign requestOf fs) I)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : I db)
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg) :
    I finalCfg.globalDb ∧
      ∃ events,
        finalCfg.globalDb =
          List.foldl (fun current req => fs req current) db (CommitLog.requests requestOf events) := by
  exact reachableRequestGraphSpecs_sound
    hStable
    hPreserve
    hSilent
    (ParallelValid.reachableCommitSpecs hValid)
    hDb
    hRun

namespace VerifiedRequestServerSpec

def requestTrace {Req : Type} (server : VerifiedRequestServerSpec Req) (events : List CommitEvent) :
    List Req :=
  CommitLog.requests server.requestOf events

def ofHandlerFamilySpec {Req : Type}
    (family : HandlerFamilySpec Req)
    (silent : ∀ db db', family.rely db db' → db' = db)
    (requestOf : TxnId → Req)
    (program : Semantics.Program)
    (valid :
      ParallelValid family.invariant family.rely program
        (RequestSpec.assign requestOf family.specs)
        family.invariant) :
    VerifiedRequestServerSpec Req where
  invariant := family.invariant
  rely := family.rely
  silent := silent
  requestOf := requestOf
  specs := family.specs
  program := program
  valid := valid

def ofTxnIndexedSpecs {Req : Type}
    (invariant : Assertion)
    (rely : Rely)
    (silent : ∀ db db', rely db db' → db' = db)
    (requestOf : TxnId → Req)
    (specs : TxnIndexedRequestSpec Req)
    (program : Semantics.Program)
    (valid :
      ParallelValid invariant rely program
        (fun txnId => specs (requestOf txnId) txnId)
        invariant) :
    VerifiedRequestServerSpec Req where
  invariant := invariant
  rely := rely
  silent := silent
  requestOf := requestOf
  specs := RequestSpec.hideTxnIds requestOf specs
  program := program
  valid := parallelValid_hideTxnIds valid

theorem doneInvariant {Req : Type} (server : VerifiedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg)
    (hDone : ProgramDone finalCfg.program) :
    server.invariant finalCfg.globalDb := by
  exact ParallelValid.invariant server.valid hDb hRun hDone

theorem commitLog {Req : Type} (server : VerifiedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events,
      CommitLog (RequestSpec.assign server.requestOf server.specs) db events finalCfg.globalDb := by
  exact parallelValid_commitLog server.silent server.valid hDb hRun

theorem requestEvents {Req : Type} (server : VerifiedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events : List CommitEvent,
      (∀ (event : CommitEvent), event ∈ events →
        server.specs (server.requestOf event.txnId) event.before event.after) := by
  rcases server.commitLog hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.requests_match_specs hLog⟩

end VerifiedRequestServerSpec

namespace VerifiedTxnIndexedRequestServerSpec

def hideTxnIds {Req : Type} (server : VerifiedTxnIndexedRequestServerSpec Req) :
    VerifiedRequestServerSpec Req :=
  VerifiedRequestServerSpec.ofTxnIndexedSpecs
    server.invariant
    server.rely
    server.silent
    server.requestOf
    server.specs
    server.program
    server.valid

theorem doneInvariant {Req : Type} (server : VerifiedTxnIndexedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg)
    (hDone : ProgramDone finalCfg.program) :
    server.invariant finalCfg.globalDb := by
  exact ParallelValid.invariant server.valid hDb hRun hDone

theorem commitLog {Req : Type} (server : VerifiedTxnIndexedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events,
      CommitLog
        (fun txnId => server.specs (server.requestOf txnId) txnId)
        db events finalCfg.globalDb := by
  exact parallelValid_commitLog server.silent server.valid hDb hRun

theorem requestEventsExact {Req : Type} (server : VerifiedTxnIndexedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events : List CommitEvent,
      ∀ event ∈ events,
        server.specs (server.requestOf event.txnId) event.txnId event.before event.after := by
  rcases server.commitLog hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.events_match_specs hLog⟩

theorem requestEvents {Req : Type} (server : VerifiedTxnIndexedRequestServerSpec Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events : List CommitEvent,
      ∀ event ∈ events,
        (RequestSpec.hideTxnIds server.requestOf server.specs)
          (server.requestOf event.txnId) event.before event.after := by
  simpa using (VerifiedRequestServerSpec.requestEvents (hideTxnIds server) hDb hRun)

end VerifiedTxnIndexedRequestServerSpec

namespace VerifiedRequestServer

def requestTrace {Req : Type} (server : VerifiedRequestServer Req) (events : List CommitEvent) :
    List Req :=
  CommitLog.requests server.requestOf events

def ofHandlerFamily {Req : Type}
    (family : HandlerFamily Req)
    (silent : ∀ db db', family.rely db db' → db' = db)
    (requestOf : TxnId → Req)
    (program : Semantics.Program)
    (valid :
      ParallelValid family.invariant family.rely program
        (RequestSpec.graphAssign requestOf family.transformer)
        family.invariant) :
    VerifiedRequestServer Req where
  invariant := family.invariant
  rely := family.rely
  silent := silent
  requestOf := requestOf
  transformer := family.transformer
  program := program
  stable := family.stable
  preserve := family.preserve
  valid := valid

def toSpec {Req : Type} (server : VerifiedRequestServer Req) : VerifiedRequestServerSpec Req where
  invariant := server.invariant
  rely := server.rely
  silent := server.silent
  requestOf := server.requestOf
  specs := fun req => StateSpec.graph (server.transformer req)
  program := server.program
  valid := by
    simpa [RequestSpec.graphAssign, RequestSpec.assign] using server.valid

theorem sound {Req : Type} (server : VerifiedRequestServer Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    server.invariant finalCfg.globalDb ∧
      ∃ events,
        finalCfg.globalDb =
          List.foldl (fun current req => server.transformer req current) db (server.requestTrace events) := by
  exact parallelValid_requestGraphSpecs_sound
    server.stable
    server.preserve
    server.silent
    server.valid
    hDb
    hRun

theorem commitLog {Req : Type} (server : VerifiedRequestServer Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events,
      CommitLog (RequestSpec.graphAssign server.requestOf server.transformer) db events finalCfg.globalDb := by
  exact parallelValid_commitLog server.silent server.valid hDb hRun

theorem requestEvents {Req : Type} (server : VerifiedRequestServer Req)
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : server.invariant db)
    (hRun : GlobalMultiStep server.rely ⟨server.program, db⟩ finalCfg) :
    ∃ events : List CommitEvent,
      ∀ event ∈ events,
        event.after = server.transformer (server.requestOf event.txnId) event.before := by
  rcases server.commitLog hDb hRun with ⟨events, hLog⟩
  exact ⟨events, CommitLog.graphAssign_implies_eventEq hLog⟩

theorem txnParallelValid_of_handlerRefines_at {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSpecAt : ∀ db db', spec db db' → specs txnId db db')
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValid Ipre R (.txn txnId isolation body) specs Ipost := by
  intro db hDb
  rcases h db hDb with ⟨hPost, hTxn⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    have hNonPar : NonParallel finalCfg.program := by
      exact globalMultiStep_preserves_nonParallel hRun (by simp [NonParallel])
    have hSkip : finalCfg.program = (Command.skip : Semantics.Program) := by
      exact programDone_eq_skip_of_nonParallel hDone hNonPar
    exact hPost finalCfg hRun hSkip
  · intro midCfg nextProgram nextDb txnId' hRun hCommit
    have hNonPar : NonParallel midCfg.program := by
      exact globalMultiStep_preserves_nonParallel hRun (by simp [NonParallel])
    have hSingle : SingleTxnProgram txnId midCfg.program := by
      exact globalMultiStep_preserves_singleTxn hRun SingleTxnProgram.txn
    have hTxnIdEq : txnId' = txnId := by
      exact txnCommitStep_txnId_eq_of_singleTxn hSingle hCommit
    rcases txnCommitStep_of_nonParallel hNonPar hCommit with
      ⟨isolation', localDb, snapshot, hProgram, hNext, hDbEq, hCommitGuard⟩
    have hStep : Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb := by
      rw [hProgram, hNext, hDbEq]
      exact Semantics.Step.txnCommit hCommitGuard
    subst hTxnIdEq
    exact hSpecAt _ _ (hTxn midCfg nextProgram nextDb hRun hStep hNext)

end VerifiedRequestServer

theorem txnParallelValid_of_handlerRefines_at {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSpecAt : ∀ db db', spec db db' → specs txnId db db')
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValid Ipre R (.txn txnId isolation body) specs Ipost := by
  exact VerifiedRequestServer.txnParallelValid_of_handlerRefines_at hSpecAt h

theorem txnParallelValid_of_handlerRefines {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValid Ipre R (.txn txnId isolation body) (fun _ => spec) Ipost := by
  exact txnParallelValid_of_handlerRefines_at
    (fun _ _ hSpec => hSpec)
    h

theorem txnParallelValidTR_of_handlerRefines_at {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (hSpecAt : ∀ db db', spec db db' → specs txnId db db')
    (h : HandlerRefinesTR Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValidTR Ipre R (.txn txnId isolation body) specs Ipost := by
  intro db hDb
  rcases h db hDb with ⟨hPost, hTxn⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    have hSingle : SingleTxnProgram txnId finalCfg.program := by
      exact globalMultiStepTR_preserves_singleTxn hRun SingleTxnProgram.txn
    have hNonPar : NonParallel finalCfg.program := by
      exact singleTxn_nonParallel hSingle
    have hSkip : finalCfg.program = (Command.skip : Semantics.Program) := by
      exact programDone_eq_skip_of_nonParallel hDone hNonPar
    exact hPost finalCfg hRun hSkip
  · intro midCfg nextProgram nextDb txnId' hRun hCommit
    have hSingle : SingleTxnProgram txnId midCfg.program := by
      exact globalMultiStepTR_preserves_singleTxn hRun SingleTxnProgram.txn
    have hTxnIdEq : txnId' = txnId := by
      exact txnCommitStep_txnId_eq_of_singleTxn hSingle hCommit
    rcases txnCommitStep_of_nonParallel (singleTxn_nonParallel hSingle) hCommit with
      ⟨_, _, _, hProgram, hNext, hDbEq, hCommitGuard⟩
    have hStep : Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb := by
      rw [hProgram, hNext, hDbEq]
      exact Semantics.Step.txnCommit hCommitGuard
    subst hTxnIdEq
    exact hSpecAt _ _ (hTxn midCfg nextProgram nextDb hRun hStep hNext)

theorem txnParallelValidTR_of_handlerRefines {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefinesTR Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValidTR Ipre R (.txn txnId isolation body) (fun _ => spec) Ipost := by
  exact txnParallelValidTR_of_handlerRefines_at
    (fun _ _ hSpec => hSpec)
    h

theorem parallelValid_par_skip_right {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost) :
    ParallelValid Ipre R (.par program (Command.skip : Semantics.Program)) specs Ipost := by
  intro db hDb
  rcases h db hDb with ⟨hPost, hCommit⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases globalMultiStep_par_skip_right hRun with ⟨finalProgram, hProgram, hRun'⟩
    rw [hProgram] at hDone
    exact hPost ⟨finalProgram, finalCfg.globalDb⟩ hRun' (programDone_par_skip_right_inv hDone)
  · intro midCfg nextProgram nextDb txnId hRun hCommitStep
    rcases globalMultiStep_par_skip_right hRun with ⟨midProgram, hProgram, hRun'⟩
    rcases txnCommitStep_par_skip_right (by simpa [hProgram] using hCommitStep) with
      ⟨nextInner, hNextEq, hCommitInner⟩
    subst hNextEq
    exact hCommit ⟨midProgram, midCfg.globalDb⟩ nextInner nextDb txnId hRun' hCommitInner

/-- TR-style first-commit theorem for a parallel pair of transactions. If the pair runs without any
earlier commit and then commits, that commit is justified by the corresponding single-transaction
proof under the other transaction's guarantee. This is the first half of the Appendix B
`RG-Par` argument. -/
theorem txnPair_firstCommitSpec {I : Assertion} {R : Rely}
    {txnIdLeft txnIdRight : TxnId}
    {isolationLeft isolationRight : IsolationSpec Database}
    {bodyLeft bodyRight : Semantics.Program}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hI : I db)
    (hLeft :
      HandlerRefines I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hRight :
      HandlerRefines I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I)
    (hPrefix :
      CommitFreeGlobalMultiStep R
        ⟨(.par
            (.txn txnIdLeft isolationLeft bodyLeft)
            (.txn txnIdRight isolationRight bodyRight) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    (actualTxnId = txnIdLeft ∧ GLeft midCfg.globalDb nextDb) ∨
      (actualTxnId = txnIdRight ∧ GRight midCfg.globalDb nextDb) := by
  rcases commitFreePrefix_firstCommit_view hPrefix hCommit with
    hLeftView | hRightView
  · rcases hLeftView with
      ⟨leftMid, rightMid, leftNext, _hMidProgram, hLeftRun, hLeftCommit, _hNextProgram⟩
    have hSingle :
        SingleTxnProgram txnIdLeft leftMid := by
      exact globalMultiStep_preserves_singleTxn hLeftRun SingleTxnProgram.txn
    have hTxnIdEq : actualTxnId = txnIdLeft := by
      exact txnCommitStep_txnId_eq_of_singleTxn hSingle hLeftCommit
    have hNonPar : NonParallel leftMid := by
      exact singleTxn_nonParallel hSingle
    rcases txnCommitStep_of_nonParallel hNonPar hLeftCommit with
      ⟨_, _, _, _hProgram, hLeftNextSkip, _hDbEq, _hCommitGuard⟩
    have hRunAug :
        GlobalMultiStep (fun db db' => R db db' ∨ GRight db db')
          ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
          ⟨leftMid, midCfg.globalDb⟩ := by
      exact globalMultiStep_mono (fun _ _ hR => Or.inl hR) hLeftRun
    rcases hLeft db hI with ⟨_hPost, hTxnGuaranteed⟩
    have hSpec :
        GLeft midCfg.globalDb nextDb := by
      exact hTxnGuaranteed
        ⟨leftMid, midCfg.globalDb⟩
        leftNext
        nextDb
        hRunAug
        (TxnCommitStep.step hLeftCommit)
        hLeftNextSkip
    exact Or.inl ⟨hTxnIdEq, hSpec⟩
  · rcases hRightView with
      ⟨leftMid, rightMid, rightNext, _hMidProgram, hRightRun, hRightCommit, _hNextProgram⟩
    have hSingle :
        SingleTxnProgram txnIdRight rightMid := by
      exact globalMultiStep_preserves_singleTxn hRightRun SingleTxnProgram.txn
    have hTxnIdEq : actualTxnId = txnIdRight := by
      exact txnCommitStep_txnId_eq_of_singleTxn hSingle hRightCommit
    have hNonPar : NonParallel rightMid := by
      exact singleTxn_nonParallel hSingle
    rcases txnCommitStep_of_nonParallel hNonPar hRightCommit with
      ⟨_, _, _, _hProgram, hRightNextSkip, _hDbEq, _hCommitGuard⟩
    have hRunAug :
        GlobalMultiStep (fun db db' => R db db' ∨ GLeft db db')
          ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
          ⟨rightMid, midCfg.globalDb⟩ := by
      exact globalMultiStep_mono (fun _ _ hR => Or.inl hR) hRightRun
    rcases hRight db hI with ⟨_hPost, hTxnGuaranteed⟩
    have hSpec :
        GRight midCfg.globalDb nextDb := by
      exact hTxnGuaranteed
        ⟨rightMid, midCfg.globalDb⟩
        rightNext
        nextDb
        hRunAug
        (TxnCommitStep.step hRightCommit)
        hRightNextSkip
    exact Or.inr ⟨hTxnIdEq, hSpec⟩

theorem txnPair_firstCommitSpecTR {I : Assertion} {R : Rely}
    {txnIdLeft txnIdRight : TxnId}
    {isolationLeft isolationRight : IsolationSpec Database}
    {bodyLeft bodyRight : Semantics.Program}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hI : I db)
    (hLeft :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hRight :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I)
    (hPrefix :
      CommitFreeGlobalMultiStepTR R
        ⟨(.par
            (.txn txnIdLeft isolationLeft bodyLeft)
            (.txn txnIdRight isolationRight bodyRight) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    (actualTxnId = txnIdLeft ∧ GLeft midCfg.globalDb nextDb) ∨
      (actualTxnId = txnIdRight ∧ GRight midCfg.globalDb nextDb) := by
  rcases commitFreePrefix_firstCommit_viewTR hPrefix hCommit with
    hLeftView | hRightView
  · rcases hLeftView with
      ⟨leftMid, rightMid, leftNext, _hMidProgram, hLeftRun, hLeftCommit, _hNextProgram⟩
    have hRunAug :
        GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
          ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
          ⟨leftMid, midCfg.globalDb⟩ := by
      exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
    rcases txnCommitSpec_of_handlerRefinesTR hLeft hI hRunAug hLeftCommit with
      ⟨hTxnIdEq, hSpec⟩
    exact Or.inl ⟨hTxnIdEq, hSpec⟩
  · rcases hRightView with
      ⟨leftMid, rightMid, rightNext, _hMidProgram, hRightRun, hRightCommit, _hNextProgram⟩
    have hRunAug :
        GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
          ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
          ⟨rightMid, midCfg.globalDb⟩ := by
      exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
    rcases txnCommitSpec_of_handlerRefinesTR hRight hI hRunAug hRightCommit with
      ⟨hTxnIdEq, hSpec⟩
    exact Or.inr ⟨hTxnIdEq, hSpec⟩

/-- Generalized second-phase rule for `skip || t`: if the remaining transaction already has a
standalone run under the augmented rely, then any later commit in the parallel configuration is
justified by the same handler proof. This isolates the only extra ingredient still needed for a full
RG-Par theorem under the current server semantics. -/
theorem txnRightCommitSpec_after_leftCommitted_from_state {I : Assertion} {R : Rely}
    {txnIdRight : TxnId}
    {isolationRight : IsolationSpec Database}
    {bodyRight : Semantics.Program}
    {rightStart : Semantics.Program} {startDb : Database}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hStartI : I startDb)
    (hRight :
      HandlerRefines I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I)
    (hStandalone :
      GlobalMultiStep (fun db db' => R db db' ∨ GLeft db db')
        ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), startDb⟩
        ⟨rightStart, db⟩)
    (hRun :
      GlobalMultiStep R
        ⟨(.par
            (Command.skip : Semantics.Program)
            rightStart : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdRight ∧ GRight midCfg.globalDb nextDb := by
  rcases globalMultiStep_par_skip_left hRun with ⟨rightMid, hMidProgram, hRightRun⟩
  rcases txnCommitStep_par_skip_left (by simpa [hMidProgram] using hCommit) with
    ⟨rightNext, hNextProgram, hRightCommit⟩
  have hRightRunAug :
      GlobalMultiStep (fun db db' => R db db' ∨ GLeft db db')
        ⟨rightStart, db⟩
        ⟨rightMid, midCfg.globalDb⟩ := by
    exact globalMultiStep_mono (fun _ _ hR => Or.inl hR) hRightRun
  have hReach :
      GlobalMultiStep (fun db db' => R db db' ∨ GLeft db db')
        ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), startDb⟩
        ⟨rightMid, midCfg.globalDb⟩ := by
    exact MultiStep.trans hStandalone hRightRunAug
  rcases txnCommitSpec_of_handlerRefines hRight hStartI hReach hRightCommit with
    ⟨hTxnIdEq, hSpec⟩
  exact ⟨hTxnIdEq, hSpec⟩

theorem txnRightCommitSpec_after_leftCommitted_from_stateTR {I : Assertion} {R : Rely}
    {txnIdRight : TxnId}
    {isolationRight : IsolationSpec Database}
    {bodyRight : Semantics.Program}
    {rightStart : Semantics.Program} {startDb : Database}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hStartI : I startDb)
    (hRight :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I)
    (hStandalone :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
        ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), startDb⟩
        ⟨rightStart, db⟩)
    (hRun :
      GlobalMultiStepTR R
        ⟨(.par
            (Command.skip : Semantics.Program)
            rightStart : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdRight ∧ GRight midCfg.globalDb nextDb := by
  rcases globalMultiStepTR_par_skip_left hRun with ⟨rightMid, hMidProgram, hRightRun⟩
  rcases txnCommitStep_par_skip_left (by simpa [hMidProgram] using hCommit) with
    ⟨rightNext, _hNextProgram, hRightCommit⟩
  have hRightRunAug :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
        ⟨rightStart, db⟩
        ⟨rightMid, midCfg.globalDb⟩ := by
    exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
  have hReach :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
        ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), startDb⟩
        ⟨rightMid, midCfg.globalDb⟩ := by
    exact MultiStep.trans hStandalone hRightRunAug
  rcases txnCommitSpec_of_handlerRefinesTR hRight hStartI hReach hRightCommit with
    ⟨hTxnIdEq, hSpec⟩
  exact ⟨hTxnIdEq, hSpec⟩

/-- Symmetric generalized second-phase rule for `t || skip`. -/
theorem txnLeftCommitSpec_after_rightCommitted_from_state {I : Assertion} {R : Rely}
    {txnIdLeft : TxnId}
    {isolationLeft : IsolationSpec Database}
    {bodyLeft : Semantics.Program}
    {leftStart : Semantics.Program} {startDb : Database}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hStartI : I startDb)
    (hLeft :
      HandlerRefines I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hStandalone :
      GlobalMultiStep (fun db db' => R db db' ∨ GRight db db')
        ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), startDb⟩
        ⟨leftStart, db⟩)
    (hRun :
      GlobalMultiStep R
        ⟨(.par
            leftStart
            (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdLeft ∧ GLeft midCfg.globalDb nextDb := by
  rcases globalMultiStep_par_skip_right hRun with ⟨leftMid, hMidProgram, hLeftRun⟩
  rcases txnCommitStep_par_skip_right (by simpa [hMidProgram] using hCommit) with
    ⟨leftNext, hNextProgram, hLeftCommit⟩
  have hLeftRunAug :
      GlobalMultiStep (fun db db' => R db db' ∨ GRight db db')
        ⟨leftStart, db⟩
        ⟨leftMid, midCfg.globalDb⟩ := by
    exact globalMultiStep_mono (fun _ _ hR => Or.inl hR) hLeftRun
  have hReach :
      GlobalMultiStep (fun db db' => R db db' ∨ GRight db db')
        ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), startDb⟩
        ⟨leftMid, midCfg.globalDb⟩ := by
    exact MultiStep.trans hStandalone hLeftRunAug
  rcases txnCommitSpec_of_handlerRefines hLeft hStartI hReach hLeftCommit with
    ⟨hTxnIdEq, hSpec⟩
  exact ⟨hTxnIdEq, hSpec⟩

theorem txnLeftCommitSpec_after_rightCommitted_from_stateTR {I : Assertion} {R : Rely}
    {txnIdLeft : TxnId}
    {isolationLeft : IsolationSpec Database}
    {bodyLeft : Semantics.Program}
    {leftStart : Semantics.Program} {startDb : Database}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hStartI : I startDb)
    (hLeft :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hStandalone :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
        ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), startDb⟩
        ⟨leftStart, db⟩)
    (hRun :
      GlobalMultiStepTR R
        ⟨(.par
            leftStart
            (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdLeft ∧ GLeft midCfg.globalDb nextDb := by
  rcases globalMultiStepTR_par_skip_right hRun with ⟨leftMid, hMidProgram, hLeftRun⟩
  rcases txnCommitStep_par_skip_right (by simpa [hMidProgram] using hCommit) with
    ⟨leftNext, _hNextProgram, hLeftCommit⟩
  have hLeftRunAug :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
        ⟨leftStart, db⟩
        ⟨leftMid, midCfg.globalDb⟩ := by
    exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
  have hReach :
      GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
        ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), startDb⟩
        ⟨leftMid, midCfg.globalDb⟩ := by
    exact MultiStep.trans hStandalone hLeftRunAug
  rcases txnCommitSpec_of_handlerRefinesTR hLeft hStartI hReach hLeftCommit with
    ⟨hTxnIdEq, hSpec⟩
  exact ⟨hTxnIdEq, hSpec⟩

/-- TR-faithful packaging of the two-transaction RG-Par proof: every commit reachable from the
parallel pair is explained by exactly one of the two component guarantees. -/
theorem txnPair_reachableCommitSpecsTR {I : Assertion} {R : Rely}
    {txnIdLeft txnIdRight : TxnId}
    {isolationLeft isolationRight : IsolationSpec Database}
    {bodyLeft bodyRight : Semantics.Program}
    {GLeft GRight : StateSpec}
    (hLeft :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hRight :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I) :
    ReachableCommitSpecsTR I R
      (.par
        (.txn txnIdLeft isolationLeft bodyLeft)
        (.txn txnIdRight isolationRight bodyRight) : Semantics.Program)
      (CombinedSpecs (ExactTxnSpec txnIdLeft GLeft) (ExactTxnSpec txnIdRight GRight)) := by
  intro db hI midCfg nextProgram nextDb actualTxnId hRun hCommit
  rcases globalMultiStepTR_split_first_commit hRun with hNoCommit | hSplit
  · simpa [CombinedSpecs, ExactTxnSpec] using
      (txnPair_firstCommitSpecTR hI hLeft hRight hNoCommit hCommit)
  · rcases hSplit with
      ⟨firstMidCfg, firstNextCfg, _firstTxnId, hPrefix, _hFirstStep, hFirstCommit, hTail⟩
    rcases commitFreePrefix_firstCommit_viewTR hPrefix hFirstCommit with
      hLeftFirst | hRightFirst
    · rcases hLeftFirst with
        ⟨leftMid, rightMid, leftNext, hMidProgram, hLeftRun, hLeftCommit, hNextProgram⟩
      rcases commitFreeGlobalMultiStepTR_project_right hPrefix with
        ⟨leftMid', rightMid', hMidProgramRight, hRightRun⟩
      have hSame :
          (.par leftMid rightMid : Semantics.Program) =
            (.par leftMid' rightMid' : Semantics.Program) := by
        simpa [hMidProgram] using hMidProgramRight
      cases hSame
      have hLeftRunAug :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
            ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
            ⟨leftMid, firstMidCfg.globalDb⟩ := by
        exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
      rcases txnCommitSpec_of_handlerRefinesTR hLeft hI hLeftRunAug hLeftCommit with
        ⟨_hLeftTxnIdEq, hFirstSpec⟩
      have hLeftSingle : SingleTxnProgram txnIdLeft leftMid := by
        exact globalMultiStepTR_preserves_singleTxn hLeftRun SingleTxnProgram.txn
      rcases txnCommitStep_of_nonParallel (singleTxn_nonParallel hLeftSingle) hLeftCommit with
        ⟨_, _, _, _hProgramEq, hLeftNextSkip, _hFlushEq, _hGuard⟩
      have hFirstNextProgram :
          firstNextCfg.program =
            (.par
              (Command.skip : Semantics.Program)
              rightMid : Semantics.Program) := by
        simpa [hLeftNextSkip] using hNextProgram
      have hRightRunAugBefore :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
            ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
            ⟨rightMid, firstMidCfg.globalDb⟩ := by
        exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
      have hRightStandalone :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
            ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
            ⟨rightMid, firstNextCfg.globalDb⟩ := by
        exact globalMultiStepTR_append_rely hRightRunAugBefore (Or.inr hFirstSpec)
      have hSecondPhase :
          GlobalMultiStepTR R
            ⟨(.par
                (Command.skip : Semantics.Program)
                rightMid : Semantics.Program), firstNextCfg.globalDb⟩
            midCfg := by
        cases firstNextCfg with
        | mk program db' =>
            simp at hFirstNextProgram
            simpa [hFirstNextProgram] using hTail
      rcases txnRightCommitSpec_after_leftCommitted_from_stateTR
          hI hRight hRightStandalone hSecondPhase hCommit with
        ⟨hTxnIdEq, hSpec⟩
      exact Or.inr ⟨hTxnIdEq, hSpec⟩
    · rcases hRightFirst with
        ⟨leftMid, rightMid, rightNext, hMidProgram, hRightRun, hRightCommit, hNextProgram⟩
      rcases commitFreeGlobalMultiStepTR_project_left hPrefix with
        ⟨leftMid', rightMid', hMidProgramLeft, hLeftRun⟩
      have hSame :
          (.par leftMid rightMid : Semantics.Program) =
            (.par leftMid' rightMid' : Semantics.Program) := by
        simpa [hMidProgram] using hMidProgramLeft
      cases hSame
      have hRightRunAug :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
            ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
            ⟨rightMid, firstMidCfg.globalDb⟩ := by
        exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
      rcases txnCommitSpec_of_handlerRefinesTR hRight hI hRightRunAug hRightCommit with
        ⟨_hRightTxnIdEq, hFirstSpec⟩
      have hRightSingle : SingleTxnProgram txnIdRight rightMid := by
        exact globalMultiStepTR_preserves_singleTxn hRightRun SingleTxnProgram.txn
      rcases txnCommitStep_of_nonParallel (singleTxn_nonParallel hRightSingle) hRightCommit with
        ⟨_, _, _, _hProgramEq, hRightNextSkip, _hFlushEq, _hGuard⟩
      have hFirstNextProgram :
          firstNextCfg.program =
            (.par
              leftMid
              (Command.skip : Semantics.Program) : Semantics.Program) := by
        simpa [hRightNextSkip] using hNextProgram
      have hLeftRunAugBefore :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
            ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
            ⟨leftMid, firstMidCfg.globalDb⟩ := by
        exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
      have hLeftStandalone :
          GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
            ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
            ⟨leftMid, firstNextCfg.globalDb⟩ := by
        exact globalMultiStepTR_append_rely hLeftRunAugBefore (Or.inr hFirstSpec)
      have hSecondPhase :
          GlobalMultiStepTR R
            ⟨(.par
                leftMid
                (Command.skip : Semantics.Program) : Semantics.Program), firstNextCfg.globalDb⟩
            midCfg := by
        cases firstNextCfg with
        | mk program db' =>
            simp at hFirstNextProgram
            simpa [hFirstNextProgram] using hTail
      rcases txnLeftCommitSpec_after_rightCommitted_from_stateTR
          hI hLeft hLeftStandalone hSecondPhase hCommit with
        ⟨hTxnIdEq, hSpec⟩
      exact Or.inl ⟨hTxnIdEq, hSpec⟩

/-- TR-faithful server validity for a parallel pair of transactions. This is the packaged Appendix
C.14 theorem for the server layer: the pair preserves the invariant and every commit belongs to the
appropriate component guarantee. -/
theorem txnPair_parallelValidTR {I : Assertion} {R : Rely}
    {txnIdLeft txnIdRight : TxnId}
    {isolationLeft isolationRight : IsolationSpec Database}
    {bodyLeft bodyRight : Semantics.Program}
    {GLeft GRight : StateSpec}
    (hLeft :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hRight :
      HandlerRefinesTR I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I) :
    ParallelValidTR I R
      (.par
        (.txn txnIdLeft isolationLeft bodyLeft)
        (.txn txnIdRight isolationRight bodyRight) : Semantics.Program)
      (CombinedSpecs (ExactTxnSpec txnIdLeft GLeft) (ExactTxnSpec txnIdRight GRight))
      I := by
  intro db hI
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases globalMultiStepTR_split_first_commit hRun with hNoCommit | hSplit
    · exact False.elim <|
        commitFreeGlobalMultiStepTR_par_notDone_of_leftTxn
          SingleTxnProgram.txn
          (by simp)
          hNoCommit
          hDone
    · rcases hSplit with
        ⟨firstMidCfg, firstNextCfg, _firstTxnId, hPrefix, _hFirstStep, hFirstCommit, hTail⟩
      rcases commitFreePrefix_firstCommit_viewTR hPrefix hFirstCommit with
        hLeftFirst | hRightFirst
      · rcases hLeftFirst with
          ⟨leftMid, rightMid, leftNext, hMidProgram, hLeftRun, hLeftCommit, hNextProgram⟩
        rcases commitFreeGlobalMultiStepTR_project_right hPrefix with
          ⟨leftMid', rightMid', hMidProgramRight, hRightRun⟩
        have hSame :
            (.par leftMid rightMid : Semantics.Program) =
              (.par leftMid' rightMid' : Semantics.Program) := by
          simpa [hMidProgram] using hMidProgramRight
        cases hSame
        have hLeftRunAug :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
              ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
              ⟨leftMid, firstMidCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
        rcases txnCommitSpec_of_handlerRefinesTR hLeft hI hLeftRunAug hLeftCommit with
          ⟨_hLeftTxnIdEq, hFirstSpec⟩
        have hLeftSingle : SingleTxnProgram txnIdLeft leftMid := by
          exact globalMultiStepTR_preserves_singleTxn hLeftRun SingleTxnProgram.txn
        rcases txnCommitStep_of_nonParallel (singleTxn_nonParallel hLeftSingle) hLeftCommit with
          ⟨_, _, _, _hProgramEq, hLeftNextSkip, _hFlushEq, _hGuard⟩
        have hFirstNextProgram :
            firstNextCfg.program =
              (.par
                (Command.skip : Semantics.Program)
                rightMid : Semantics.Program) := by
          simpa [hLeftNextSkip] using hNextProgram
        have hRightRunAugBefore :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
              ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
              ⟨rightMid, firstMidCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
        have hRightStandalone :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
              ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
              ⟨rightMid, firstNextCfg.globalDb⟩ := by
          exact globalMultiStepTR_append_rely hRightRunAugBefore (Or.inr hFirstSpec)
        have hSecondPhase :
            GlobalMultiStepTR R
              ⟨(.par
                  (Command.skip : Semantics.Program)
                  rightMid : Semantics.Program), firstNextCfg.globalDb⟩
              finalCfg := by
          cases firstNextCfg with
          | mk program db' =>
              simp at hFirstNextProgram
              simpa [hFirstNextProgram] using hTail
        rcases globalMultiStepTR_par_skip_left hSecondPhase with
          ⟨finalRight, hFinalProgram, hRightTail⟩
        have hRightTailAug :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
              ⟨rightMid, firstNextCfg.globalDb⟩
              ⟨finalRight, finalCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightTail
        have hRightFull :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
              ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
              ⟨finalRight, finalCfg.globalDb⟩ := by
          exact MultiStep.trans hRightStandalone hRightTailAug
        have hDoneRight : ProgramDone finalRight := by
          rw [hFinalProgram] at hDone
          exact programDone_par_skip_left_inv hDone
        have hSingleFinalRight : SingleTxnProgram txnIdRight finalRight := by
          exact globalMultiStepTR_preserves_singleTxn hRightFull SingleTxnProgram.txn
        have hFinalRightSkip :
            finalRight = (Command.skip : Semantics.Program) := by
          exact programDone_eq_skip_of_nonParallel hDoneRight
            (singleTxn_nonParallel hSingleFinalRight)
        exact (hRight db hI).1 ⟨finalRight, finalCfg.globalDb⟩ hRightFull hFinalRightSkip
      · rcases hRightFirst with
          ⟨leftMid, rightMid, rightNext, hMidProgram, hRightRun, hRightCommit, hNextProgram⟩
        rcases commitFreeGlobalMultiStepTR_project_left hPrefix with
          ⟨leftMid', rightMid', hMidProgramLeft, hLeftRun⟩
        have hSame :
            (.par leftMid rightMid : Semantics.Program) =
              (.par leftMid' rightMid' : Semantics.Program) := by
          simpa [hMidProgram] using hMidProgramLeft
        cases hSame
        have hRightRunAug :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GLeft db db')
              ⟨(.txn txnIdRight isolationRight bodyRight : Semantics.Program), db⟩
              ⟨rightMid, firstMidCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hRightRun
        rcases txnCommitSpec_of_handlerRefinesTR hRight hI hRightRunAug hRightCommit with
          ⟨_hRightTxnIdEq, hFirstSpec⟩
        have hRightSingle : SingleTxnProgram txnIdRight rightMid := by
          exact globalMultiStepTR_preserves_singleTxn hRightRun SingleTxnProgram.txn
        rcases txnCommitStep_of_nonParallel (singleTxn_nonParallel hRightSingle) hRightCommit with
          ⟨_, _, _, _hProgramEq, hRightNextSkip, _hFlushEq, _hGuard⟩
        have hFirstNextProgram :
            firstNextCfg.program =
              (.par
                leftMid
                (Command.skip : Semantics.Program) : Semantics.Program) := by
          simpa [hRightNextSkip] using hNextProgram
        have hLeftRunAugBefore :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
              ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
              ⟨leftMid, firstMidCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftRun
        have hLeftStandalone :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
              ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
              ⟨leftMid, firstNextCfg.globalDb⟩ := by
          exact globalMultiStepTR_append_rely hLeftRunAugBefore (Or.inr hFirstSpec)
        have hSecondPhase :
            GlobalMultiStepTR R
              ⟨(.par
                  leftMid
                  (Command.skip : Semantics.Program) : Semantics.Program), firstNextCfg.globalDb⟩
              finalCfg := by
          cases firstNextCfg with
          | mk program db' =>
              simp at hFirstNextProgram
              simpa [hFirstNextProgram] using hTail
        rcases globalMultiStepTR_par_skip_right hSecondPhase with
          ⟨finalLeft, hFinalProgram, hLeftTail⟩
        have hLeftTailAug :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
              ⟨leftMid, firstNextCfg.globalDb⟩
              ⟨finalLeft, finalCfg.globalDb⟩ := by
          exact globalMultiStepTR_mono (fun _ _ hR => Or.inl hR) hLeftTail
        have hLeftFull :
            GlobalMultiStepTR (fun db db' => R db db' ∨ GRight db db')
              ⟨(.txn txnIdLeft isolationLeft bodyLeft : Semantics.Program), db⟩
              ⟨finalLeft, finalCfg.globalDb⟩ := by
          exact MultiStep.trans hLeftStandalone hLeftTailAug
        have hDoneLeft : ProgramDone finalLeft := by
          rw [hFinalProgram] at hDone
          exact programDone_par_skip_right_inv hDone
        have hSingleFinalLeft : SingleTxnProgram txnIdLeft finalLeft := by
          exact globalMultiStepTR_preserves_singleTxn hLeftFull SingleTxnProgram.txn
        have hFinalLeftSkip :
            finalLeft = (Command.skip : Semantics.Program) := by
          exact programDone_eq_skip_of_nonParallel hDoneLeft
            (singleTxn_nonParallel hSingleFinalLeft)
        exact (hLeft db hI).1 ⟨finalLeft, finalCfg.globalDb⟩ hLeftFull hFinalLeftSkip
  · intro midCfg nextProgram nextDb txnId hRun hCommit
    exact txnPair_reachableCommitSpecsTR hLeft hRight db hI midCfg nextProgram nextDb txnId hRun hCommit

/-- Once the left branch has already terminated, any subsequent commit in `skip || t` must come from
the remaining right transaction and is justified by its single-transaction proof. -/
theorem txnRightCommitSpec_after_leftCommitted {I : Assertion} {R : Rely}
    {txnIdRight : TxnId}
    {isolationRight : IsolationSpec Database}
    {bodyRight : Semantics.Program}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hI : I db)
    (hRight :
      HandlerRefines I (fun db db' => R db db' ∨ GLeft db db')
        (.txn txnIdRight isolationRight bodyRight)
        GRight
        I)
    (hRun :
      GlobalMultiStep R
        ⟨(.par
            (Command.skip : Semantics.Program)
            (.txn txnIdRight isolationRight bodyRight) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdRight ∧ GRight midCfg.globalDb nextDb := by
  exact txnRightCommitSpec_after_leftCommitted_from_state
    hI
    hRight
    MultiStep.refl
    hRun
    hCommit

/-- Symmetric version of `txnRightCommitSpec_after_leftCommitted` for `t || skip`. -/
theorem txnLeftCommitSpec_after_rightCommitted {I : Assertion} {R : Rely}
    {txnIdLeft : TxnId}
    {isolationLeft : IsolationSpec Database}
    {bodyLeft : Semantics.Program}
    {GLeft GRight : StateSpec}
    {db : Database} {midCfg : GlobalConfig}
    {nextProgram : Semantics.Program} {nextDb : Database}
    {actualTxnId : TxnId}
    (hI : I db)
    (hLeft :
      HandlerRefines I (fun db db' => R db db' ∨ GRight db db')
        (.txn txnIdLeft isolationLeft bodyLeft)
        GLeft
        I)
    (hRun :
      GlobalMultiStep R
        ⟨(.par
            (.txn txnIdLeft isolationLeft bodyLeft)
            (Command.skip : Semantics.Program) : Semantics.Program), db⟩
        midCfg)
    (hCommit :
      TxnCommitStep actualTxnId
        midCfg.program
        midCfg.globalDb
        nextProgram
        nextDb) :
    actualTxnId = txnIdLeft ∧ GLeft midCfg.globalDb nextDb := by
  exact txnLeftCommitSpec_after_rightCommitted_from_state
    hI
    hLeft
    MultiStep.refl
    hRun
    hCommit

end Server

end DbAppProgramLogic
