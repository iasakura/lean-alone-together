import DbAppProgramLogic.Logic

namespace DbAppProgramLogic

/-!
Paper-faithful server-facing wrappers built on the canonical POPL'18 global semantics.

This file intentionally stays thin. It does not introduce an alternative machine model; instead it
repackages `Logic.GlobalValid` for talking about committed handler specifications and, for now,
provides only the minimal parallel/server notions that are directly supported by the corrected core
logic.
-/

/-- Relational specification for one committed handler: pre-state to post-state. -/
abbrev StateSpec := Database → Database → Prop

/-- Functional state transformer used when a relational spec is the graph of a function. -/
abbrev StateTransformer := Database → Database

/-- Request-indexed relational specifications. -/
abbrev RequestSpec (Req : Type) := Req → StateSpec

/-- Request-indexed state transformers. -/
abbrev RequestTransformer (Req : Type) := Req → StateTransformer

/-- A request family whose exact specification may mention the concrete transaction id. -/
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

/-- Server-level wrappers reuse the canonical quiescence and commit-event notions from `Logic`. -/
abbrev ProgramDone := Logic.ProgramDone
abbrev TxnCommitStep := Logic.TxnCommitStep
abbrev SingleTxnProgram := Logic.SingleTxnProgram

theorem singleTxn_done_eq_skip {txnId : TxnId} {program : Semantics.Program}
    (hSingle : SingleTxnProgram txnId program)
    (hDone : ProgramDone program) :
    program = (Command.skip : Semantics.Program) :=
  Logic.singleTxn_done_eq_skip hSingle hDone

theorem globalMultiStep_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂)
    (hSingle : SingleTxnProgram txnId cfg₁.program) :
    SingleTxnProgram txnId cfg₂.program :=
  Logic.globalMultiStep_preserves_singleTxn hRun hSingle

theorem txnCommitStep_of_singleTxn {txnId actualTxnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hSingle : SingleTxnProgram txnId program)
    (hCommit : TxnCommitStep actualTxnId program db program' db') :
    actualTxnId = txnId ∧ Semantics.Step program db program' db' ∧
      program' = (Command.skip : Semantics.Program) :=
  Logic.txnCommitStep_of_singleTxn hSingle hCommit

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

end CommitLog

/-- Handler-level correctness is just the canonical global validity judgment. -/
abbrev HandlerRefines := Logic.GlobalValid

/-- Parallel/server validity: quiescent endpoints satisfy the postcondition, and every commit event
matches the per-transaction specification family. -/
def ParallelValid (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (specs : TxnId → StateSpec) (Ipost : Assertion) : Prop :=
  ∀ db,
    Ipre db →
      (∀ finalCfg,
        GlobalMultiStep R ⟨program, db⟩ finalCfg →
        ProgramDone finalCfg.program →
        Ipost finalCfg.globalDb) ∧
      (∀ txnId midCfg nextProgram nextDb,
        GlobalMultiStep R ⟨program, db⟩ midCfg →
        TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
        specs txnId midCfg.globalDb nextDb)

theorem ParallelValid.invariant {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost)
    {db : Database} (hDb : Ipre db)
    {finalCfg : GlobalConfig}
    (hRun : GlobalMultiStep R ⟨program, db⟩ finalCfg)
    (hDone : ProgramDone finalCfg.program) :
    Ipost finalCfg.globalDb :=
  (h db hDb).1 _ hRun hDone

theorem ParallelValid.commitSpec {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost)
    {db : Database} (hDb : Ipre db)
    {txnId : TxnId} {midCfg : GlobalConfig} {nextProgram : Semantics.Program} {nextDb : Database}
    (hRun : GlobalMultiStep R ⟨program, db⟩ midCfg)
    (hCommit : TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb) :
    specs txnId midCfg.globalDb nextDb :=
  (h db hDb).2 _ _ _ _ hRun hCommit

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
    have hSingleFinal :
        SingleTxnProgram txnId finalCfg.program := by
      exact globalMultiStep_preserves_singleTxn hRun SingleTxnProgram.txn
    exact hPost _ hRun hDone
  · intro actualTxnId midCfg nextProgram nextDb hRun hCommit
    have hSingleMid :
        SingleTxnProgram txnId midCfg.program := by
      exact globalMultiStep_preserves_singleTxn hRun SingleTxnProgram.txn
    rcases txnCommitStep_of_singleTxn hSingleMid hCommit with ⟨rfl, _hStep, _hSkip⟩
    exact hSpecAt _ _ (hTxn _ _ _ _ hRun hCommit)

theorem txnParallelValid_of_handlerRefines {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValid Ipre R (.txn txnId isolation body) (fun _ => spec) Ipost := by
  exact txnParallelValid_of_handlerRefines_at (fun _ _ hSpec => hSpec) h

/-- The rely relation induced by a family of commit specifications. -/
def SpecsRely (specs : TxnId → StateSpec) : Rely :=
  fun db db' => ∃ txnId, specs txnId db db'

/-- Pointwise disjunction of two commit-specification families. -/
def CombinedSpecs (leftSpecs rightSpecs : TxnId → StateSpec) : TxnId → StateSpec :=
  fun txnId db db' => leftSpecs txnId db db' ∨ rightSpecs txnId db db'

/-- A specification family that singles out one concrete transaction id. -/
def ExactTxnSpec (txnId : TxnId) (spec : StateSpec) : TxnId → StateSpec :=
  fun txnId' db db' => txnId' = txnId ∧ spec db db'

theorem specsRely_exactTxnSpec_iff {txnId : TxnId} {spec : StateSpec}
    {db db' : Database} :
    SpecsRely (ExactTxnSpec txnId spec) db db' ↔ spec db db' := by
  constructor
  · rintro ⟨txnId', hEq, hSpec⟩
    subst hEq
    exact hSpec
  · intro hSpec
    exact ⟨txnId, rfl, hSpec⟩

/-- Every actual top-level step either preserves the outer database or corresponds to a commit
event. This is the basic case split behind RG-style parallel composition. -/
theorem step_sameDb_or_commit
    {program program' : Semantics.Program} {db db' : Database}
    (hStep : Semantics.Step program db program' db') :
    db' = db ∨ ∃ txnId, TxnCommitStep txnId program db program' db' := by
  induction hStep with
  | txnStart =>
      exact Or.inl rfl
  | txnExec =>
      exact Or.inl rfl
  | txnCommit hCommit =>
      exact Or.inr ⟨_, TxnCommitStep.root hCommit⟩
  | parLeft hInner ih =>
      rcases ih with hSame | ⟨txnId, hCommit⟩
      · exact Or.inl hSame
      · exact Or.inr ⟨txnId, TxnCommitStep.parLeft hCommit⟩
  | parRight hInner ih =>
      rcases ih with hSame | ⟨txnId, hCommit⟩
      · exact Or.inl hSame
      · exact Or.inr ⟨txnId, TxnCommitStep.parRight hCommit⟩

/-- Inversion lemma for top-level `par` steps. -/
theorem step_par_inv
    {left right program' : Semantics.Program} {db db' : Database}
    (hStep : Semantics.Step (.par left right) db program' db') :
    (∃ left', program' = (.par left' right : Semantics.Program) ∧
        Semantics.Step left db left' db') ∨
      (∃ right', program' = (.par left right' : Semantics.Program) ∧
        Semantics.Step right db right' db') := by
  cases hStep with
  | parLeft hLeft =>
      exact Or.inl ⟨_, rfl, hLeft⟩
  | parRight hRight =>
      exact Or.inr ⟨_, rfl, hRight⟩

/-- A run of `left || right` can be projected to each branch separately. Sibling non-commit steps
become stuttering, while sibling commits become rely steps justified by the sibling spec family. -/
theorem parallel_run_projects
    {I : Assertion} {R : Rely}
    {left right : Semantics.Program}
    {leftSpecs rightSpecs : TxnId → StateSpec}
    {db : Database} (hDb : I db)
    (hLeft :
      ParallelValid I
        (fun db db' => R db db' ∨ SpecsRely rightSpecs db db')
        left leftSpecs I)
    (hRight :
      ParallelValid I
        (fun db db' => R db db' ∨ SpecsRely leftSpecs db db')
        right rightSpecs I)
    {finalCfg : GlobalConfig}
    (hRun : GlobalMultiStep R ⟨(.par left right : Semantics.Program), db⟩ finalCfg) :
    ∃ left' right',
      finalCfg.program = (.par left' right' : Semantics.Program) ∧
      GlobalMultiStep
        (fun db db' => R db db' ∨ SpecsRely rightSpecs db db')
        ⟨left, db⟩
        ⟨left', finalCfg.globalDb⟩ ∧
      GlobalMultiStep
        (fun db db' => R db db' ∨ SpecsRely leftSpecs db db')
        ⟨right, db⟩
        ⟨right', finalCfg.globalDb⟩ := by
  induction hRun with
  | refl =>
      exact ⟨left, right, rfl, MultiStep.refl, MultiStep.refl⟩
  | @tail cfg₂ cfg₃ hPrev hLast ih =>
      rcases ih with ⟨left₂, right₂, hProgram₂, hLeftRun₂, hRightRun₂⟩
      cases hCfg₂ : cfg₂ with
      | mk program₂ db₂ =>
          subst cfg₂
          have hProgram₂' : program₂ = (.par left₂ right₂ : Semantics.Program) := by
            simpa using hProgram₂
          subst program₂
          cases hCfg₃ : cfg₃ with
          | mk program₃ db₃ =>
              subst cfg₃
              cases hLast with
              | inl hActual =>
                  have hActual' :
                      Semantics.Step
                        (.par left₂ right₂ : Semantics.Program)
                        db₂
                        program₃
                        db₃ := by
                    simpa using hActual
                  rcases step_par_inv hActual' with
                    ⟨left₃, rfl, hLeftStep⟩ | ⟨right₃, rfl, hRightStep⟩
                  ·
                      rcases step_sameDb_or_commit hLeftStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          by simpa [hSameDb] using hRightRun₂⟩
                      · have hLeftSpec : leftSpecs txnId db₂ db₃ := by
                          exact ParallelValid.commitSpec hLeft hDb hLeftRun₂ hCommit
                        exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          MultiStep.tail hRightRun₂
                            (Or.inr ⟨rfl, Or.inr ⟨txnId, hLeftSpec⟩⟩)⟩
                  ·
                      rcases step_sameDb_or_commit hRightStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₂, right₃, rfl,
                          by simpa [hSameDb] using hLeftRun₂,
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
                      · have hRightSpec : rightSpecs txnId db₂ db₃ := by
                          exact ParallelValid.commitSpec hRight hDb hRightRun₂ hCommit
                        exact ⟨left₂, right₃, rfl,
                          MultiStep.tail hLeftRun₂
                            (Or.inr ⟨rfl, Or.inr ⟨txnId, hRightSpec⟩⟩),
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
              | inr hRely =>
                  rcases hRely with ⟨hProgram, hRely⟩
                  have hProgram₃ :
                      program₃ = (.par left₂ right₂ : Semantics.Program) := by
                    simpa using hProgram
                  subst program₃
                  exact ⟨left₂, right₂, rfl,
                    MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩),
                    MultiStep.tail hRightRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩)⟩

/-- Server-level parallel composition in the standard RG style: each side is verified assuming the
base rely together with the other side's commit guarantees, and the composed program is then valid
under the base rely alone. -/
theorem parallelValid_par {I : Assertion} {R : Rely}
    {left right : Semantics.Program}
    {leftSpecs rightSpecs : TxnId → StateSpec}
    (hLeft :
      ParallelValid I
        (fun db db' => R db db' ∨ SpecsRely rightSpecs db db')
        left leftSpecs I)
    (hRight :
      ParallelValid I
        (fun db db' => R db db' ∨ SpecsRely leftSpecs db db')
        right rightSpecs I) :
    ParallelValid I R
      (.par left right : Semantics.Program)
      (CombinedSpecs leftSpecs rightSpecs)
      I := by
  intro db hDb
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases parallel_run_projects hDb hLeft hRight hRun with
      ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hDone' : ProgramDone (.par left' right' : Semantics.Program) := by
      simpa [hProgram] using hDone
    cases hDone' with
    | par hDoneLeft hDoneRight =>
        exact (hLeft _ hDb).1 ⟨left', finalCfg.globalDb⟩ hLeftRun hDoneLeft
  · intro txnId midCfg nextProgram nextDb hRun hCommit
    rcases parallel_run_projects hDb hLeft hRight hRun with
      ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hCommit' :
        TxnCommitStep txnId (.par left' right' : Semantics.Program)
          midCfg.globalDb nextProgram nextDb := by
      simpa [hProgram] using hCommit
    cases hCommit' with
    | parLeft hCommitLeft =>
        exact Or.inl ((hLeft _ hDb).2 _ ⟨left', midCfg.globalDb⟩ _ _ hLeftRun hCommitLeft)
    | parRight hCommitRight =>
        exact Or.inr ((hRight _ hDb).2 _ ⟨right', midCfg.globalDb⟩ _ _ hRightRun hCommitRight)

/-- Convenient two-transaction composition rule obtained by combining `txnParallelValid` with the
general server-level `parallelValid_par` theorem. -/
theorem txnPair_parallelValid_of_handlerRefines
    {I : Assertion} {R : Rely}
    {leftTxnId rightTxnId : TxnId}
    {leftIsolation rightIsolation : IsolationSpec Database}
    {leftBody rightBody : Semantics.Program}
    {leftSpec rightSpec : StateSpec}
    (hLeft :
      HandlerRefines I
        (fun db db' => R db db' ∨ rightSpec db db')
        (.txn leftTxnId leftIsolation leftBody)
        leftSpec
        I)
    (hRight :
      HandlerRefines I
        (fun db db' => R db db' ∨ leftSpec db db')
        (.txn rightTxnId rightIsolation rightBody)
        rightSpec
        I) :
    ParallelValid I R
      (.par
        (.txn leftTxnId leftIsolation leftBody)
        (.txn rightTxnId rightIsolation rightBody)
        : Semantics.Program)
      (CombinedSpecs
        (ExactTxnSpec leftTxnId leftSpec)
        (ExactTxnSpec rightTxnId rightSpec))
      I := by
  have hLeft' :
      HandlerRefines I
        (fun db db' => R db db' ∨ SpecsRely (ExactTxnSpec rightTxnId rightSpec) db db')
        (.txn leftTxnId leftIsolation leftBody)
        leftSpec
        I := by
    refine Logic.globalValid_of_relySubset hLeft ?_
    intro db db' hRely
    rcases hRely with hRely | hRely
    · exact Or.inl hRely
    · exact Or.inr ((specsRely_exactTxnSpec_iff).1 hRely)
  have hRight' :
      HandlerRefines I
        (fun db db' => R db db' ∨ SpecsRely (ExactTxnSpec leftTxnId leftSpec) db db')
        (.txn rightTxnId rightIsolation rightBody)
        rightSpec
        I := by
    refine Logic.globalValid_of_relySubset hRight ?_
    intro db db' hRely
    rcases hRely with hRely | hRely
    · exact Or.inl hRely
    · exact Or.inr ((specsRely_exactTxnSpec_iff).1 hRely)
  exact parallelValid_par
    (txnParallelValid_of_handlerRefines_at
      (fun _ _ hSpec => ⟨rfl, hSpec⟩)
      hLeft')
    (txnParallelValid_of_handlerRefines_at
      (fun _ _ hSpec => ⟨rfl, hSpec⟩)
      hRight')

end Server

end DbAppProgramLogic
