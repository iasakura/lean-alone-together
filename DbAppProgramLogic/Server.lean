import DbAppProgramLogic.Logic

namespace DbAppProgramLogic

abbrev StateSpec := Database → Database → Prop
abbrev StateTransformer := Database → Database
abbrev RequestSpec (Req : Type) := Req → StateSpec
abbrev RequestTransformer (Req : Type) := Req → StateTransformer

namespace StateSpec

def graph (f : StateTransformer) : StateSpec :=
  fun db db' => db' = f db

end StateSpec

namespace RequestSpec

def assign {Req : Type} (requestOf : TxnId → Req) (specs : RequestSpec Req) : TxnId → StateSpec :=
  fun txnId => specs (requestOf txnId)

def graphAssign {Req : Type} (requestOf : TxnId → Req) (fs : RequestTransformer Req) :
    TxnId → StateSpec :=
  assign requestOf (fun req => StateSpec.graph (fs req))

end RequestSpec

namespace Server

open Logic

def NonParallel : Semantics.Program → Prop
  | .par _ _ => False
  | _ => True

inductive ProgramDone : Semantics.Program → Prop where
  | skip :
      ProgramDone (Command.skip : Semantics.Program)
  | par {left right : Semantics.Program} :
      ProgramDone left →
      ProgramDone right →
      ProgramDone (.par left right : Semantics.Program)

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

def HandlerRefines (P : Assertion) (R : Rely)
    (program : Semantics.Program) (spec : StateSpec) (Q : Assertion) : Prop :=
  GlobalValid P R program spec Q

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

theorem programDone_par_skip_right_inv {program : Semantics.Program}
    (hDone : ProgramDone (.par program (Command.skip : Semantics.Program))) :
    ProgramDone program := by
  cases hDone with
  | par hLeft hRight =>
      exact hLeft

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

theorem ParallelValid.reachableCommitSpecs {Ipre : Assertion} {R : Rely}
    {program : Semantics.Program} {specs : TxnId → StateSpec} {Ipost : Assertion}
    (h : ParallelValid Ipre R program specs Ipost) :
    ReachableCommitSpecs Ipre R program specs := by
  intro db hDb midCfg nextProgram nextDb txnId hRun hCommit
  exact ParallelValid.commitSpec h hDb hRun hCommit

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

theorem txnParallelValid_of_handlerRefines {Ipre : Assertion} {R : Rely}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {spec : StateSpec} {Ipost : Assertion}
    (h : HandlerRefines Ipre R (.txn txnId isolation body) spec Ipost) :
    ParallelValid Ipre R (.txn txnId isolation body) (fun _ => spec) Ipost := by
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
    rcases txnCommitStep_of_nonParallel hNonPar hCommit with
      ⟨isolation', localDb, snapshot, hProgram, hNext, hDbEq, hCommitGuard⟩
    have hStep : Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb := by
      rw [hProgram, hNext, hDbEq]
      exact Semantics.Step.txnCommit hCommitGuard
    exact hTxn midCfg nextProgram nextDb hRun hStep hNext

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

end Server

end DbAppProgramLogic
