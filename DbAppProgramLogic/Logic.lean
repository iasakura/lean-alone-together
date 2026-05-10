import DbAppProgramLogic.Semantics

namespace DbAppProgramLogic

/-!
Semantic judgments and soundness proofs for the rely-guarantee layer.

This file sits between the operational semantics and the symbolic/VCG layer. It defines
interleaved executions with explicit rely steps, semantic validity for local and global judgments,
and then proves the inductive RG systems sound.
-/

abbrev Assertion := Database → Prop
abbrev BiAssertion := Database → Database → Prop
abbrev Rely := Database → Database → Prop
abbrev LocalRely := Database → Database → Database → Prop
abbrev Guarantee := Database → Database → Prop

/-- Local configurations track the command under execution, its private delta, and the database view
currently visible to the transaction. -/
structure LocalConfig (ι : Type) where
  cmd : Command ι Database
  localDb : Database
  visibleDb : Database

/-- Global configurations are the top-level machine states used by `globalInterleavedStep`. -/
structure GlobalConfig where
  program : Semantics.Program
  globalDb : Database

namespace Logic

noncomputable local instance : DecidableEq Semantics.Program := by
  classical
  infer_instance

/-- Quiescent top-level programs: every parallel branch has terminated. -/
inductive ProgramDone : Semantics.Program → Prop where
  | skip :
      ProgramDone (Command.skip : Semantics.Program)
  | par {left right : Semantics.Program} :
      ProgramDone left →
      ProgramDone right →
      ProgramDone (.par left right : Semantics.Program)

/-- Commit events lifted through nested `par` structure. These are the semantically relevant
events that contribute to a program's guarantee relation. -/
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
  | seqLeft {txnId : TxnId} {left left' right : Semantics.Program}
      {db db' : Database} :
      TxnCommitStep txnId left db left' db' →
      TxnCommitStep txnId (.seq left right) db (.seq left' right) db'

theorem TxnCommitStep.step {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (h : TxnCommitStep txnId program db program' db') :
    Semantics.Step program db program' db' := by
  induction h with
  | root hCommit =>
      exact Semantics.Step.txnCommit hCommit
  | parLeft hInner ih =>
      exact Semantics.Step.parLeft ih
  | parRight hInner ih =>
      exact Semantics.Step.parRight ih
  | seqLeft hInner ih =>
      exact Semantics.Step.seqLeft ih

/-- Single-transaction programs never contain top-level `par`; they are exactly the shapes
reachable from one top-level `txn`. -/
inductive SingleTxnProgram (txnId : TxnId) : Semantics.Program → Prop where
  | txn {isolation : IsolationSpec Database} {body : Semantics.Program} :
      SingleTxnProgram txnId (.txn txnId isolation body)
  | runtime {isolation : IsolationSpec Database}
      {localDb snapshot : Database} {body : Semantics.Program} :
      SingleTxnProgram txnId (.txnRuntime txnId isolation localDb snapshot body)
  | skip :
      SingleTxnProgram txnId (Command.skip : Semantics.Program)

theorem singleTxn_done_eq_skip {txnId : TxnId} {program : Semantics.Program}
    (hSingle : SingleTxnProgram txnId program)
    (hDone : ProgramDone program) :
    program = (Command.skip : Semantics.Program) := by
  cases hSingle <;> cases hDone <;> rfl

inductive MultiStep (step : α → α → Prop) : α → α → Prop where
  | refl {cfg} : MultiStep step cfg cfg
  | tail {cfg₁ cfg₂ cfg₃} : MultiStep step cfg₁ cfg₂ → step cfg₂ cfg₃ → MultiStep step cfg₁ cfg₃

/-- Forward-oriented variant of `MultiStep`. Some proofs over traces are simpler in this shape. -/
inductive MultiStepFwd (step : α → α → Prop) : α → α → Prop where
  | refl {cfg} : MultiStepFwd step cfg cfg
  | cons {cfg₁ cfg₂ cfg₃} : step cfg₁ cfg₂ → MultiStepFwd step cfg₂ cfg₃ → MultiStepFwd step cfg₁ cfg₃

theorem MultiStep.mono {step step' : α → α → Prop} {cfg₁ cfg₂ : α}
    (hSub : ∀ {cfg cfg'}, step cfg cfg' → step' cfg cfg') :
    MultiStep step cfg₁ cfg₂ →
    MultiStep step' cfg₁ cfg₂ := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | tail hPrev hLast ih =>
      exact MultiStep.tail ih (hSub hLast)

/-- A standard global stability condition: `P` survives every rely step. -/
def stableAssertion (R : Rely) (P : Assertion) : Prop :=
  ∀ db db', P db → R db db' → P db'

/-- Local stability for assertions that can mention both the local delta and the visible database. -/
def stableBiAssertion (R : LocalRely) (P : BiAssertion) : Prop :=
  ∀ localDb visibleDb visibleDb', P localDb visibleDb → R localDb visibleDb visibleDb' → P localDb visibleDb'

/-- Stability for isolation relations when the environment takes an intermediate rely step.

The `MultiStep R baseDb midDb` premise restricts attention to intermediate states `midDb`
that are actually reachable from `baseDb` via rely steps. Without this restriction, the
single-step universal form would force `R` to be effectively identity for non-trivial
`I` such as snapshot isolation; the paper's stability argument for `I_ss`
(p.27:16 of 1710.09844v2) relies implicitly on reachability/monotonicity. -/
def stableIsolation (R : Rely) (I : Database → Database → Database → Prop) : Prop :=
  ∀ localDb baseDb midDb finalDb,
    MultiStep R baseDb midDb →
    I localDb baseDb finalDb →
    R midDb finalDb →
    I localDb baseDb midDb ∧ I localDb midDb finalDb

theorem stableAssertion_of_relySubset {R R' : Rely} {P : Assertion}
    (hStable : stableAssertion R P)
    (hSub : ∀ db db', R' db db' → R db db') :
    stableAssertion R' P := by
  intro db db' hP hR'
  exact hStable _ _ hP (hSub _ _ hR')

theorem stableBiAssertion_of_relySubset {R R' : LocalRely} {P : BiAssertion}
    (hStable : stableBiAssertion R P)
    (hSub : ∀ localDb visibleDb visibleDb', R' localDb visibleDb visibleDb' →
      R localDb visibleDb visibleDb') :
    stableBiAssertion R' P := by
  intro localDb visibleDb visibleDb' hP hR'
  exact hStable _ _ _ hP (hSub _ _ _ hR')

theorem stableIsolation_of_relySubset {R R' : Rely}
    {I : Database → Database → Database → Prop}
    (hStable : stableIsolation R I)
    (hSub : ∀ db db', R' db db' → R db db') :
    stableIsolation R' I := by
  intro localDb baseDb midDb finalDb hReach hI hR'
  have hReach' : MultiStep R baseDb midDb :=
    MultiStep.mono (fun {_ _} h => hSub _ _ h) hReach
  exact hStable _ _ _ _ hReach' hI (hSub _ _ hR')

/-- Restrict a global rely by the isolation guard currently required by a running transaction. -/
def relyMod (R : Rely) (I : Database → Database → Database → Prop) : LocalRely :=
  fun localDb visibleDb visibleDb' =>
    ∃ baseDb, R visibleDb visibleDb' ∧ I localDb baseDb visibleDb ∧ I localDb baseDb visibleDb'

/-- Local executions interleave actual transaction steps with environment steps that only change the
visible database. -/
def localInterleavedStep (R : LocalRely) (txnId : TxnId) :
    LocalConfig ι → LocalConfig ι → Prop
  | ⟨cmd, localDb, visibleDb⟩, ⟨cmd', localDb', visibleDb'⟩ =>
      (Semantics.LocalStep visibleDb txnId cmd localDb cmd' localDb' ∧ visibleDb' = visibleDb) ∨
        (cmd' = cmd ∧ localDb' = localDb ∧ cmd ≠ (Command.skip : Command ι Database) ∧
          R localDb visibleDb visibleDb')

theorem localInterleavedStep_mono {R R' : LocalRely} {txnId : TxnId}
    (hSub : ∀ localDb visibleDb visibleDb',
      R' localDb visibleDb visibleDb' → R localDb visibleDb visibleDb')
    {cfg cfg' : LocalConfig ι} :
    localInterleavedStep (ι := ι) R' txnId cfg cfg' →
    localInterleavedStep (ι := ι) R txnId cfg cfg' := by
  intro hStep
  cases hStep with
  | inl hActual =>
      exact Or.inl hActual
  | inr hRely =>
      rcases hRely with ⟨hCmd, hLocal, hNotSkip, hRely⟩
      exact Or.inr ⟨hCmd, hLocal, hNotSkip, hSub _ _ _ hRely⟩

/-- Paper-faithful top-level interleaving from Appendix C.2: a rely step changes only the outer
global database, leaving the program state unchanged. Runtime transaction nodes therefore keep
their cached snapshot until they themselves take an actual step. -/
def globalInterleavedStep (R : Rely) : GlobalConfig → GlobalConfig → Prop
  | ⟨program, globalDb⟩, ⟨program', globalDb'⟩ =>
      Semantics.Step program globalDb program' globalDb' ∨
        (program' = program ∧ R globalDb globalDb')

abbrev LocalMultiStep (R : LocalRely) (txnId : TxnId) (ι : Type) :=
  MultiStep (localInterleavedStep (ι := ι) R txnId)

abbrev GlobalMultiStep (R : Rely) :=
  MultiStep (globalInterleavedStep R)

theorem globalInterleavedStep_mono {R R' : Rely}
    (hSub : ∀ db db', R' db db' → R db db')
    {cfg cfg' : GlobalConfig} :
    globalInterleavedStep R' cfg cfg' →
    globalInterleavedStep R cfg cfg' := by
  intro hStep
  cases hStep with
  | inl hActual =>
      exact Or.inl hActual
  | inr hRely =>
      rcases hRely with ⟨hProgram, hR⟩
      exact Or.inr ⟨hProgram, hSub _ _ hR⟩

theorem localMultiStep_mono {R R' : LocalRely} {txnId : TxnId} {ι : Type}
    (hSub : ∀ localDb visibleDb visibleDb',
      R' localDb visibleDb visibleDb' → R localDb visibleDb visibleDb')
    {cfg cfg' : LocalConfig ι} :
    LocalMultiStep R' txnId ι cfg cfg' →
    LocalMultiStep R txnId ι cfg cfg' := by
  exact MultiStep.mono (fun hStep => localInterleavedStep_mono hSub hStep)

theorem globalMultiStep_mono {R R' : Rely}
    (hSub : ∀ db db', R' db db' → R db db')
    {cfg cfg' : GlobalConfig} :
    GlobalMultiStep R' cfg cfg' →
    GlobalMultiStep R cfg cfg' := by
  exact MultiStep.mono (fun hStep => globalInterleavedStep_mono hSub hStep)

/-- Semantic validity for local judgments: whenever the command reaches `skip`, the postcondition
holds on the final local/visible databases. -/
def LocalValid (R : LocalRely) (txnId : TxnId)
    (P : BiAssertion) (c : Command ι Database) (Q : BiAssertion) : Prop :=
  ∀ localDb visibleDb finalCfg,
    P localDb visibleDb →
    LocalMultiStep R txnId ι ⟨c, localDb, visibleDb⟩ finalCfg →
    finalCfg.cmd = (Command.skip : Command ι Database) →
    Q finalCfg.localDb finalCfg.visibleDb

/-- Semantic guarantee judgment: every transaction commit performed by `program` satisfies `G`. -/
def txnGuaranteed (R : Rely) (G : Guarantee) (program : Semantics.Program) (db : Database) : Prop :=
  ∀ txnId midCfg nextProgram nextDb,
    GlobalMultiStep R ⟨program, db⟩ midCfg →
    TxnCommitStep txnId midCfg.program midCfg.globalDb nextProgram nextDb →
    G midCfg.globalDb nextDb

/-- Semantic validity for top-level programs: the program preserves the global assertion and its
commits satisfy the guarantee relation. -/
def GlobalValid (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (G : Guarantee) (Ipost : Assertion) : Prop :=
  ∀ db,
    Ipre db →
      (∀ finalCfg,
        GlobalMultiStep R ⟨program, db⟩ finalCfg →
        ProgramDone finalCfg.program →
        Ipost finalCfg.globalDb) ∧
      txnGuaranteed R G program db

theorem txnGuaranteed_mono {R : Rely} {G G' : Guarantee}
    {program : Semantics.Program} {db : Database}
    (hTxn : txnGuaranteed R G program db)
    (hImp : ∀ db db', G db db' → G' db db') :
    txnGuaranteed R G' program db := by
  intro txnId midCfg nextProgram nextDb hMulti hStep
  exact hImp _ _ (hTxn txnId midCfg nextProgram nextDb hMulti hStep)

theorem globalValid_conseq {Ipre Imid Ipost : Assertion} {R : Rely}
    {program : Semantics.Program} {G G' : Guarantee}
    (hValid : GlobalValid Imid R program G Ipost)
    (hPre : ∀ db, Ipre db → Imid db)
    (hG : ∀ db db', G db db' → G' db db') :
    GlobalValid Ipre R program G' Ipost := by
  intro db hDb
  rcases hValid db (hPre _ hDb) with ⟨hPost, hTxn⟩
  refine ⟨hPost, txnGuaranteed_mono hTxn hG⟩

theorem globalValid_post_conseq {Ipre Ipost Ipost' : Assertion} {R : Rely}
    {program : Semantics.Program} {G : Guarantee}
    (hValid : GlobalValid Ipre R program G Ipost)
    (hPost : ∀ db, Ipost db → Ipost' db) :
    GlobalValid Ipre R program G Ipost' := by
  intro db hDb
  rcases hValid db hDb with ⟨hDone, hTxn⟩
  exact ⟨fun finalCfg hRun hProgramDone => hPost _ (hDone finalCfg hRun hProgramDone), hTxn⟩

theorem localValid_of_relySubset {R R' : LocalRely} {txnId : TxnId}
    {P : BiAssertion} {c : Command ι Database} {Q : BiAssertion}
    (hValid : LocalValid R txnId P c Q)
    (hSub : ∀ localDb visibleDb visibleDb',
      R' localDb visibleDb visibleDb' → R localDb visibleDb visibleDb') :
    LocalValid R' txnId P c Q := by
  intro localDb visibleDb finalCfg hP hRun hSkip
  exact hValid _ _ _ hP (localMultiStep_mono hSub hRun) hSkip

theorem localValid_of_stutterRely {R : LocalRely} {txnId : TxnId}
    {P : BiAssertion} {c : Command ι Database} {Q : BiAssertion}
    (hValid : LocalValid (fun _ _ _ => False) txnId P c Q)
    (hSilent : ∀ localDb visibleDb visibleDb',
      R localDb visibleDb visibleDb' → visibleDb' = visibleDb) :
    LocalValid R txnId P c Q := by
  have stripStep :
      ∀ {cfg cfg' : LocalConfig ι},
        localInterleavedStep (ι := ι) R txnId cfg cfg' →
        cfg' = cfg ∨
          localInterleavedStep (ι := ι) (fun _ _ _ => False) txnId cfg cfg' := by
    intro cfg cfg' hStep
    cases hStep with
    | inl hActual =>
        exact Or.inr (Or.inl hActual)
    | inr hRely =>
        rcases cfg with ⟨cmd, localDb, visibleDb⟩
        rcases cfg' with ⟨cmd', localDb', visibleDb'⟩
        rcases hRely with ⟨hCmd, hLocal, _hNotSkip, hR⟩
        subst hCmd
        subst hLocal
        have hVis : visibleDb' = visibleDb := hSilent _ _ _ hR
        subst hVis
        exact Or.inl rfl
  have strip :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        LocalMultiStep R txnId ι cfg₁ cfg₂ →
        LocalMultiStep (fun _ _ _ => False) txnId ι cfg₁ cfg₂ := by
    intro cfg₁ cfg₂ hRun
    induction hRun with
    | refl =>
        exact MultiStep.refl
    | tail hPrev hLast ih =>
        rcases stripStep hLast with rfl | hLast'
        · exact ih
        · exact MultiStep.tail ih hLast'
  intro localDb visibleDb finalCfg hP hRun hSkip
  exact hValid _ _ _ hP (strip hRun) hSkip

theorem txnGuaranteed_of_relySubset {R R' : Rely} {G : Guarantee}
    {program : Semantics.Program} {db : Database}
    (hTxn : txnGuaranteed R G program db)
    (hSub : ∀ db db', R' db db' → R db db') :
    txnGuaranteed R' G program db := by
  intro txnId midCfg nextProgram nextDb hMulti hStep
  exact hTxn _ _ _ _ (globalMultiStep_mono hSub hMulti) hStep

theorem globalValid_of_relySubset {Ipre Ipost : Assertion} {R R' : Rely}
    {program : Semantics.Program} {G : Guarantee}
    (hValid : GlobalValid Ipre R program G Ipost)
    (hSub : ∀ db db', R' db db' → R db db') :
    GlobalValid Ipre R' program G Ipost := by
  intro db hDb
  rcases hValid db hDb with ⟨hPost, hTxn⟩
  refine ⟨?_, txnGuaranteed_of_relySubset hTxn hSub⟩
  intro finalCfg hRun hSkip
  exact hPost _ (globalMultiStep_mono hSub hRun) hSkip

theorem localInterleavedStep_of_localStep (R : LocalRely) (txnId : TxnId)
    {cmd cmd' : Command ι Database} {localDb localDb' visibleDb : Database}
    (h : Semantics.LocalStep visibleDb txnId cmd localDb cmd' localDb') :
    localInterleavedStep (ι := ι) R txnId
      ⟨cmd, localDb, visibleDb⟩
      ⟨cmd', localDb', visibleDb⟩ := by
  exact Or.inl ⟨h, rfl⟩

theorem globalInterleavedStep_of_step (R : Rely)
    {program program' : Semantics.Program} {db db' : Database}
    (h : Semantics.Step program db program' db') :
    globalInterleavedStep R ⟨program, db⟩ ⟨program', db'⟩ := by
  exact Or.inl h

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
  | seqLeft hInner ih =>
      rcases ih with hSame | ⟨txnId, hCommit⟩
      · exact Or.inl hSame
      · exact Or.inr ⟨txnId, TxnCommitStep.seqLeft hCommit⟩
  | seqSkip =>
      exact Or.inl rfl
  | parLeft hInner ih =>
      rcases ih with hSame | ⟨txnId, hCommit⟩
      · exact Or.inl hSame
      · exact Or.inr ⟨txnId, TxnCommitStep.parLeft hCommit⟩
  | parRight hInner ih =>
      rcases ih with hSame | ⟨txnId, hCommit⟩
      · exact Or.inl hSame
      · exact Or.inr ⟨txnId, TxnCommitStep.parRight hCommit⟩

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

theorem step_preserves_singleTxn {txnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hSingle : SingleTxnProgram txnId program)
    (hStep : Semantics.Step program db program' db') :
    SingleTxnProgram txnId program' := by
  cases hSingle with
  | txn =>
      cases hStep with
      | txnStart =>
          exact SingleTxnProgram.runtime
  | runtime =>
      cases hStep with
      | txnExec hExec hLocal =>
          exact SingleTxnProgram.runtime
      | txnCommit hCommit =>
          exact SingleTxnProgram.skip
  | skip =>
      cases hStep

theorem globalInterleavedStep_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg cfg' : GlobalConfig}
    (hStep : globalInterleavedStep R cfg cfg')
    (hSingle : SingleTxnProgram txnId cfg.program) :
    SingleTxnProgram txnId cfg'.program := by
  cases hStep with
  | inl hActual =>
      exact step_preserves_singleTxn hSingle hActual
  | inr hRely =>
      rcases hRely with ⟨hProgram, _⟩
      simpa [hProgram] using hSingle

theorem globalMultiStep_preserves_singleTxn {txnId : TxnId} {R : Rely}
    {cfg₁ cfg₂ : GlobalConfig}
    (hRun : GlobalMultiStep R cfg₁ cfg₂)
    (hSingle : SingleTxnProgram txnId cfg₁.program) :
    SingleTxnProgram txnId cfg₂.program := by
  induction hRun generalizing txnId with
  | refl =>
      exact hSingle
  | tail hPrev hLast ih =>
      exact globalInterleavedStep_preserves_singleTxn hLast (ih hSingle)

theorem txnCommitStep_of_singleTxn {txnId actualTxnId : TxnId}
    {program program' : Semantics.Program} {db db' : Database}
    (hSingle : SingleTxnProgram txnId program)
    (hCommit : TxnCommitStep actualTxnId program db program' db') :
    actualTxnId = txnId ∧ Semantics.Step program db program' db' ∧
      program' = (Command.skip : Semantics.Program) := by
  cases hSingle with
  | txn =>
      cases hCommit
  | runtime =>
      cases hCommit with
      | root hCommitGuard =>
          exact ⟨rfl, Semantics.Step.txnCommit hCommitGuard, rfl⟩
  | skip =>
      cases hCommit

theorem globalValid_par {I : Assertion} {R : Rely}
    {left right : Semantics.Program} {Gleft Gright : Guarantee}
    (hLeft : GlobalValid I (fun db db' => R db db' ∨ Gright db db') left Gleft I)
    (hRight : GlobalValid I (fun db db' => R db db' ∨ Gleft db db') right Gright I) :
    GlobalValid I R (.par left right : Semantics.Program) (fun db db' => Gleft db db' ∨ Gright db db') I := by
  intro db hDb
  have hLeftPost := (hLeft db hDb).1
  have hLeftTxn := (hLeft db hDb).2
  have hRightPost := (hRight db hDb).1
  have hRightTxn := (hRight db hDb).2
  have hProject :
      ∀ {finalCfg : GlobalConfig},
        GlobalMultiStep R ⟨(.par left right : Semantics.Program), db⟩ finalCfg →
        ∃ left' right',
          finalCfg.program = (.par left' right' : Semantics.Program) ∧
          GlobalMultiStep
            (fun db db' => R db db' ∨ Gright db db')
            ⟨left, db⟩
            ⟨left', finalCfg.globalDb⟩ ∧
          GlobalMultiStep
            (fun db db' => R db db' ∨ Gleft db db')
            ⟨right, db⟩
            ⟨right', finalCfg.globalDb⟩ := by
    intro finalCfg hRun
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
                    · rcases step_sameDb_or_commit hLeftStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          by simpa [hSameDb] using hRightRun₂⟩
                      · have hGleft : Gleft db₂ db₃ := by
                          exact hLeftTxn txnId _ _ _ hLeftRun₂ hCommit
                        exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          MultiStep.tail hRightRun₂ (Or.inr ⟨rfl, Or.inr hGleft⟩)⟩
                    · rcases step_sameDb_or_commit hRightStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₂, right₃, rfl,
                          by simpa [hSameDb] using hLeftRun₂,
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
                      · have hGright : Gright db₂ db₃ := by
                          exact hRightTxn txnId _ _ _ hRightRun₂ hCommit
                        exact ⟨left₂, right₃, rfl,
                          MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, Or.inr hGright⟩),
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
                | inr hRely =>
                    rcases hRely with ⟨hProgram, hRely⟩
                    have hProgram₃ : program₃ = (.par left₂ right₂ : Semantics.Program) := by
                      simpa using hProgram
                    subst program₃
                    exact ⟨left₂, right₂, rfl,
                      MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩),
                      MultiStep.tail hRightRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩)⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases hProject hRun with ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hDone' : ProgramDone (.par left' right' : Semantics.Program) := by
      simpa [hProgram] using hDone
    cases hDone' with
    | par hDoneLeft hDoneRight =>
        exact hLeftPost ⟨left', finalCfg.globalDb⟩ hLeftRun hDoneLeft
  · intro txnId midCfg nextProgram nextDb hRun hCommit
    rcases hProject hRun with ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hCommit' :
        TxnCommitStep txnId (.par left' right' : Semantics.Program)
          midCfg.globalDb nextProgram nextDb := by
      simpa [hProgram] using hCommit
    cases hCommit' with
    | parLeft hCommitLeft =>
        exact Or.inl (hLeftTxn _ ⟨left', midCfg.globalDb⟩ _ _ hLeftRun hCommitLeft)
    | parRight hCommitRight =>
        exact Or.inr (hRightTxn _ ⟨right', midCfg.globalDb⟩ _ _ hRightRun hCommitRight)

theorem globalValid_par2 {Ileft Iright IpostLeft IpostRight : Assertion} {R : Rely}
    {left right : Semantics.Program} {Gleft Gright : Guarantee}
    (hLeft :
      GlobalValid Ileft (fun db db' => R db db' ∨ Gright db db') left Gleft IpostLeft)
    (hRight :
      GlobalValid Iright (fun db db' => R db db' ∨ Gleft db db') right Gright IpostRight) :
    GlobalValid
      (fun db => Ileft db ∧ Iright db)
      R
      (.par left right : Semantics.Program)
      (fun db db' => Gleft db db' ∨ Gright db db')
      (fun db => IpostLeft db ∧ IpostRight db) := by
  intro db hDb
  have hLeftPost := (hLeft db hDb.1).1
  have hLeftTxn := (hLeft db hDb.1).2
  have hRightPost := (hRight db hDb.2).1
  have hRightTxn := (hRight db hDb.2).2
  have hProject :
      ∀ {finalCfg : GlobalConfig},
        GlobalMultiStep R ⟨(.par left right : Semantics.Program), db⟩ finalCfg →
        ∃ left' right',
          finalCfg.program = (.par left' right' : Semantics.Program) ∧
          GlobalMultiStep
            (fun db db' => R db db' ∨ Gright db db')
            ⟨left, db⟩
            ⟨left', finalCfg.globalDb⟩ ∧
          GlobalMultiStep
            (fun db db' => R db db' ∨ Gleft db db')
            ⟨right, db⟩
            ⟨right', finalCfg.globalDb⟩ := by
    intro finalCfg hRun
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
                    · rcases step_sameDb_or_commit hLeftStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          by simpa [hSameDb] using hRightRun₂⟩
                      · have hGleft : Gleft db₂ db₃ := by
                          exact hLeftTxn txnId _ _ _ hLeftRun₂ hCommit
                        exact ⟨left₃, right₂, rfl,
                          MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step _ hLeftStep),
                          MultiStep.tail hRightRun₂ (Or.inr ⟨rfl, Or.inr hGleft⟩)⟩
                    · rcases step_sameDb_or_commit hRightStep with hSameDb | ⟨txnId, hCommit⟩
                      · exact ⟨left₂, right₃, rfl,
                          by simpa [hSameDb] using hLeftRun₂,
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
                      · have hGright : Gright db₂ db₃ := by
                          exact hRightTxn txnId _ _ _ hRightRun₂ hCommit
                        exact ⟨left₂, right₃, rfl,
                          MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, Or.inr hGright⟩),
                          MultiStep.tail hRightRun₂ (globalInterleavedStep_of_step _ hRightStep)⟩
                | inr hRely =>
                    rcases hRely with ⟨hProgram, hRely⟩
                    have hProgram₃ : program₃ = (.par left₂ right₂ : Semantics.Program) := by
                      simpa using hProgram
                    subst program₃
                    exact ⟨left₂, right₂, rfl,
                      MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩),
                      MultiStep.tail hRightRun₂ (Or.inr ⟨rfl, Or.inl hRely⟩)⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases hProject hRun with ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hDone' : ProgramDone (.par left' right' : Semantics.Program) := by
      simpa [hProgram] using hDone
    cases hDone' with
    | par hDoneLeft hDoneRight =>
        exact
          ⟨ hLeftPost ⟨left', finalCfg.globalDb⟩ hLeftRun hDoneLeft
          , hRightPost ⟨right', finalCfg.globalDb⟩ hRightRun hDoneRight
          ⟩
  · intro txnId midCfg nextProgram nextDb hRun hCommit
    rcases hProject hRun with ⟨left', right', hProgram, hLeftRun, hRightRun⟩
    have hCommit' :
        TxnCommitStep txnId (.par left' right' : Semantics.Program)
          midCfg.globalDb nextProgram nextDb := by
      simpa [hProgram] using hCommit
    cases hCommit' with
    | parLeft hCommitLeft =>
        exact Or.inl (hLeftTxn _ ⟨left', midCfg.globalDb⟩ _ _ hLeftRun hCommitLeft)
    | parRight hCommitRight =>
        exact Or.inr (hRightTxn _ ⟨right', midCfg.globalDb⟩ _ _ hRightRun hCommitRight)

theorem globalValid_seq {Ipre Imid Ipost : Assertion} {R : Rely}
    {left right : Semantics.Program} {Gleft Gright : Guarantee}
    (hLeft : GlobalValid Ipre R left Gleft Imid)
    (hRight : GlobalValid Imid R right Gright Ipost) :
    GlobalValid Ipre R (.seq left right : Semantics.Program)
      (fun db db' => Gleft db db' ∨ Gright db db') Ipost := by
  intro db hDb
  have hLeftPost := (hLeft db hDb).1
  have hLeftTxn := (hLeft db hDb).2
  have hProject :
      ∀ {cfg : GlobalConfig},
        GlobalMultiStep R ⟨(.seq left right : Semantics.Program), db⟩ cfg →
          (∃ left',
            cfg.program = (.seq left' right : Semantics.Program) ∧
            GlobalMultiStep R ⟨left, db⟩ ⟨left', cfg.globalDb⟩) ∨
          (∃ midDb right',
            GlobalMultiStep R ⟨left, db⟩ ⟨(Command.skip : Semantics.Program), midDb⟩ ∧
            cfg.program = right' ∧
            GlobalMultiStep R ⟨right, midDb⟩ ⟨right', cfg.globalDb⟩) := by
    intro cfg hRun
    induction hRun with
    | refl =>
        exact Or.inl ⟨left, rfl, MultiStep.refl⟩
    | @tail cfg₂ cfg₃ hPrev hLast ih =>
        cases hCfg₂ : cfg₂ with
        | mk program₂ db₂ =>
            subst cfg₂
            rcases ih with hBefore | hAfter
            · rcases hBefore with ⟨left₂, hProgram₂, hLeftRun₂⟩
              have hProgram₂' : program₂ = (.seq left₂ right : Semantics.Program) := by
                simpa using hProgram₂
              subst program₂
              cases hCfg₃ : cfg₃ with
              | mk program₃ db₃ =>
                  subst cfg₃
                  cases hLast with
                  | inl hActual =>
                      have hActual' :
                          Semantics.Step (.seq left₂ right : Semantics.Program)
                            db₂ program₃ db₃ := by
                        simpa using hActual
                      cases hActual' with
                      | seqLeft hStepLeft =>
                          exact Or.inl ⟨_, rfl,
                            MultiStep.tail hLeftRun₂ (globalInterleavedStep_of_step R hStepLeft)⟩
                      | seqSkip =>
                          exact Or.inr ⟨db₂, right, hLeftRun₂, rfl, MultiStep.refl⟩
                  | inr hRely =>
                      rcases hRely with ⟨hProgram₃, hR⟩
                      have hProgram₃' : program₃ = (.seq left₂ right : Semantics.Program) := by
                        simpa using hProgram₃
                      subst program₃
                      exact Or.inl ⟨left₂, rfl,
                        MultiStep.tail hLeftRun₂ (Or.inr ⟨rfl, hR⟩)⟩
            · rcases hAfter with ⟨midDb, right₂, hLeftRun, hProgram₂, hRightRun₂⟩
              have hProgram₂' : program₂ = right₂ := by
                simpa using hProgram₂
              subst program₂
              cases hCfg₃ : cfg₃ with
              | mk program₃ db₃ =>
                  subst cfg₃
                  have hRightStep :
                      globalInterleavedStep R ⟨right₂, db₂⟩ ⟨program₃, db₃⟩ := by
                    simpa using hLast
                  exact Or.inr ⟨midDb, program₃, hLeftRun, rfl,
                    MultiStep.tail hRightRun₂ hRightStep⟩
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun hDone
    rcases hProject hRun with hBefore | hAfter
    · rcases hBefore with ⟨left', hProgram, _hLeftRun⟩
      have hDoneSeq : ProgramDone (.seq left' right : Semantics.Program) := by
        simpa [hProgram] using hDone
      cases hDoneSeq
    · rcases hAfter with ⟨midDb, right', hLeftRun, hProgram, hRightRun⟩
      have hImid : Imid midDb := by
        exact hLeftPost ⟨(Command.skip : Semantics.Program), midDb⟩ hLeftRun ProgramDone.skip
      have hRightPost := (hRight midDb hImid).1
      have hDoneRight : ProgramDone right' := by
        simpa [hProgram] using hDone
      exact hRightPost ⟨right', finalCfg.globalDb⟩ hRightRun hDoneRight
  · intro txnId midCfg nextProgram nextDb hRun hCommit
    rcases hProject hRun with hBefore | hAfter
    · rcases hBefore with ⟨left', hProgram, hLeftRun⟩
      have hCommit' :
          TxnCommitStep txnId (.seq left' right : Semantics.Program)
            midCfg.globalDb nextProgram nextDb := by
        simpa [hProgram] using hCommit
      cases hCommit' with
      | seqLeft hCommitLeft =>
          exact Or.inl (hLeftTxn _ ⟨left', midCfg.globalDb⟩ _ _ hLeftRun hCommitLeft)
    · rcases hAfter with ⟨midDb, right', hLeftRun, hProgram, hRightRun⟩
      have hCommitRight :
          TxnCommitStep txnId right' midCfg.globalDb nextProgram nextDb := by
        simpa [hProgram] using hCommit
      have hImid : Imid midDb := by
        exact hLeftPost ⟨(Command.skip : Semantics.Program), midDb⟩ hLeftRun ProgramDone.skip
      have hRightTxn := (hRight midDb hImid).2
      exact Or.inr (hRightTxn _ ⟨right', midCfg.globalDb⟩ _ _ hRightRun hCommitRight)

theorem no_step_from_program_skip
    {db db' : Database} {program' : Semantics.Program} :
    ¬ Semantics.Step (Command.skip : Semantics.Program) db program' db' := by
  intro h
  cases h

theorem step_txn_inv {txnId : TxnId} {isolation : IsolationSpec Database}
    {body : Semantics.Program} {db db' : Database} {program' : Semantics.Program}
    (h : Semantics.Step (.txn txnId isolation body) db program' db') :
    program' = (.txnRuntime txnId isolation [] db body : Semantics.Program) ∧ db' = db := by
  cases h with
  | txnStart =>
      exact ⟨rfl, rfl⟩

theorem step_txnRuntime_inv {txnId : TxnId} {isolation : IsolationSpec Database}
    {localDb snapshot currentDb : Database} {currentBody program' : Semantics.Program} {db' : Database}
    (h :
      Semantics.Step (.txnRuntime txnId isolation localDb snapshot currentBody) currentDb program' db') :
    (∃ body' localDb',
        currentBody ≠ (Command.skip : Semantics.Program) ∧
        program' = (.txnRuntime txnId isolation localDb' currentDb body' : Semantics.Program) ∧
        db' = currentDb ∧
        Semantics.LocalStep currentDb txnId currentBody localDb body' localDb') ∨
      (currentBody = (Command.skip : Semantics.Program) ∧
        program' = (Command.skip : Semantics.Program) ∧
        db' = Database.flush localDb currentDb ∧
        isolation.commit localDb snapshot currentDb) := by
  cases h with
  | txnExec hExec hLocal =>
      left
      refine ⟨_, _, ?_, rfl, rfl, ?_⟩
      · intro hSkip
        cases hSkip
        cases hLocal
      · simpa using hLocal
  | txnCommit hCommit =>
      right
      exact ⟨rfl, rfl, rfl, hCommit⟩

theorem step_txnRuntime_inv_full {txnId : TxnId} {isolation : IsolationSpec Database}
    {localDb snapshot currentDb : Database} {currentBody program' : Semantics.Program} {db' : Database}
    (h :
      Semantics.Step (.txnRuntime txnId isolation localDb snapshot currentBody) currentDb program' db') :
    (∃ body' localDb',
        currentBody ≠ (Command.skip : Semantics.Program) ∧
        program' = (.txnRuntime txnId isolation localDb' currentDb body' : Semantics.Program) ∧
        db' = currentDb ∧
        isolation.exec localDb snapshot currentDb ∧
        Semantics.LocalStep currentDb txnId currentBody localDb body' localDb') ∨
      (currentBody = (Command.skip : Semantics.Program) ∧
        program' = (Command.skip : Semantics.Program) ∧
        db' = Database.flush localDb currentDb ∧
        isolation.commit localDb snapshot currentDb) := by
  cases h with
  | txnExec hExec hLocal =>
      left
      refine ⟨_, _, ?_, rfl, rfl, hExec, hLocal⟩
      intro hSkip
      cases hSkip
      cases hLocal
  | txnCommit hCommit =>
      right
      exact ⟨rfl, rfl, rfl, hCommit⟩

theorem skipGlobalFwd_preserves (R : Rely) (I : Assertion)
    (hStable : stableAssertion R I)
    {db : Database} {finalCfg : GlobalConfig}
    (hPath :
      MultiStepFwd (globalInterleavedStep R)
        ⟨(Command.skip : Semantics.Program), db⟩ finalCfg)
    (hI : I db) :
    finalCfg.program = (Command.skip : Semantics.Program) ∧ I finalCfg.globalDb := by
  have hAux :
      ∀ {cfg₁ cfg₂ : GlobalConfig},
        MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
        cfg₁.program = (Command.skip : Semantics.Program) →
        I cfg₁.globalDb →
        cfg₂.program = (Command.skip : Semantics.Program) ∧ I cfg₂.globalDb := by
    intro cfg₁ cfg₂ hPath'
    induction hPath' with
    | refl =>
        intro hSkip hI'
        exact ⟨hSkip, hI'⟩
    | @cons cfg₁ cfgMid cfgFinal hStep hRest ih =>
        intro hSkip hI'
        cases cfg₁ with
        | mk program₁ db₁ =>
            cases hSkip
            cases cfgMid with
            | mk programMid dbMid =>
                cases hStep with
                | inl hActual =>
                    exact False.elim (no_step_from_program_skip hActual)
                | inr hRely =>
                    rcases hRely with ⟨hProgram, hR⟩
                    have hEqProgram : programMid = (Command.skip : Semantics.Program) := by
                      simpa using hProgram
                    have hI'' : I dbMid := by
                      exact hStable _ _ hI' hR
                    exact ih hEqProgram hI''
  exact hAux hPath rfl hI

theorem localStep_strip_prefix_aux (txnId : TxnId)
    {cmd cmd' : Command ι Database} {startLocalDb localDb' visibleDb : Database}
    (h : Semantics.LocalStep visibleDb txnId cmd startLocalDb cmd' localDb')
    (prefixDb baseLocalDb : Database)
    (hStart : startLocalDb = prefixDb ++ baseLocalDb) :
    ∃ strippedLocalDb,
      localDb' = prefixDb ++ strippedLocalDb ∧
      Semantics.LocalStep visibleDb txnId cmd baseLocalDb cmd' strippedLocalDb := by
  induction h generalizing prefixDb baseLocalDb with
  | letE hEval =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.letE hEval⟩
  | iteTrue hEval =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.iteTrue hEval⟩
  | iteFalse hEval =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.iteFalse hEval⟩
  | seqLeft hStep ih =>
      rcases ih prefixDb baseLocalDb hStart with ⟨strippedLocalDb, hEq, hStep'⟩
      exact ⟨strippedLocalDb, hEq, Semantics.LocalStep.seqLeft hStep'⟩
  | seqSkip =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.seqSkip⟩
  | insert hEval hFresh =>
      rename_i expr record startLocalDb
      cases hStart
      refine ⟨baseLocalDb ++ [Row.fromInsert txnId record], ?_, ?_⟩
      · simp [List.append_assoc]
      · exact Semantics.LocalStep.insert hEval
          (_root_.DbAppProgramLogic.Semantics.insertFresh_append_left
            (snapshot := visibleDb)
            (prefixDb := prefixDb)
            (localDb := baseLocalDb)
            (record := record)
            hFresh)
  | select hSelect =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.select hSelect⟩
  | delete hDelete hDisjoint =>
      rename_i source predicate startLocalDb removed
      cases hStart
      refine ⟨baseLocalDb ++ removed, ?_, ?_⟩
      · simp [List.append_assoc]
      · exact Semantics.LocalStep.delete hDelete
          (_root_.DbAppProgramLogic.Database.disjointIds_append_left
            prefixDb baseLocalDb removed hDisjoint)
  | update hUpdate hDisjoint =>
      rename_i source updateExpr predicate startLocalDb updated
      cases hStart
      refine ⟨baseLocalDb ++ updated, ?_, ?_⟩
      · simp [List.append_assoc]
      · exact Semantics.LocalStep.update hUpdate
          (_root_.DbAppProgramLogic.Database.disjointIds_append_left
            prefixDb baseLocalDb updated hDisjoint)
  | foreachStart hEval =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.foreachStart hEval⟩
  | foreachNext =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.foreachNext⟩
  | foreachDone =>
      cases hStart
      exact ⟨baseLocalDb, rfl, Semantics.LocalStep.foreachDone⟩

theorem localStep_strip_prefix (txnId : TxnId) (prefixDb : Database)
    {cmd cmd' : Command ι Database} {baseLocalDb localDb' visibleDb : Database}
    (h : Semantics.LocalStep visibleDb txnId cmd (prefixDb ++ baseLocalDb) cmd' localDb') :
    ∃ strippedLocalDb,
      localDb' = prefixDb ++ strippedLocalDb ∧
      Semantics.LocalStep visibleDb txnId cmd baseLocalDb cmd' strippedLocalDb := by
  exact localStep_strip_prefix_aux txnId h prefixDb baseLocalDb rfl

theorem localInterleavedStep_strip_prefix_false (txnId : TxnId) (prefixDb : Database)
    {cmd cmd' : Command ι Database}
    {baseLocalDb localDb' visibleDb visibleDb' : Database}
    (h :
      localInterleavedStep (ι := ι) (fun _ _ _ => False) txnId
        ⟨cmd, prefixDb ++ baseLocalDb, visibleDb⟩
        ⟨cmd', localDb', visibleDb'⟩) :
    ∃ strippedLocalDb,
      localDb' = prefixDb ++ strippedLocalDb ∧
      localInterleavedStep (ι := ι) (fun _ _ _ => False) txnId
        ⟨cmd, baseLocalDb, visibleDb⟩
        ⟨cmd', strippedLocalDb, visibleDb'⟩ := by
  cases h with
  | inl hLocal =>
      rcases hLocal with ⟨hLocal, hVisibleEq⟩
      rcases localStep_strip_prefix (ι := ι) txnId prefixDb hLocal with
        ⟨strippedLocalDb, hEq, hLocal'⟩
      exact ⟨strippedLocalDb, hEq, Or.inl ⟨hLocal', hVisibleEq⟩⟩
  | inr hRely =>
      exact False.elim hRely.2.2.2

theorem localMultiStep_strip_prefix_false (txnId : TxnId) (prefixDb : Database)
    {cmd : Command ι Database} {baseLocalDb visibleDb : Database}
    {finalCfg : LocalConfig ι}
    (h :
      LocalMultiStep (fun _ _ _ => False) txnId ι
        ⟨cmd, prefixDb ++ baseLocalDb, visibleDb⟩ finalCfg) :
    ∃ strippedLocalDb,
      finalCfg.localDb = prefixDb ++ strippedLocalDb ∧
      LocalMultiStep (fun _ _ _ => False) txnId ι
        ⟨cmd, baseLocalDb, visibleDb⟩
        ⟨finalCfg.cmd, strippedLocalDb, finalCfg.visibleDb⟩ := by
  induction h with
  | refl =>
      exact ⟨baseLocalDb, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfg₂ cfg₃
      cases cfg₂ with
      | mk midCmd midDb midVisible =>
          rcases ih with ⟨midLocalDb, hMidEq, hPrev'⟩
          simp at hMidEq
          cases hMidEq
          rcases localInterleavedStep_strip_prefix_false (ι := ι) txnId prefixDb hLast with
            ⟨strippedLocalDb, hEq, hLast'⟩
          exact ⟨strippedLocalDb, hEq, MultiStep.tail hPrev' hLast'⟩

theorem localValid_prepend_false (txnId : TxnId) (prefixDb visibleDb deltaDb : Database)
    (c : Command ι Database)
    (h :
      LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ visible = visibleDb)
        c
        (fun localDb visible => localDb = deltaDb ∧ visible = visibleDb)) :
    LocalValid (fun _ _ _ => False) txnId
      (fun localDb visible => localDb = prefixDb ∧ visible = visibleDb)
      c
      (fun localDb visible => localDb = prefixDb ++ deltaDb ∧ visible = visibleDb) := by
  intro localDb visibleDb' finalCfg hPre hMulti hSkip
  rcases hPre with ⟨hLocalEq, hVisibleEq⟩
  subst localDb
  subst visibleDb'
  have hMultiPrefixed :
      LocalMultiStep (fun _ _ _ => False) txnId ι
        ⟨c, prefixDb ++ [], visibleDb⟩ finalCfg := by
    simpa using hMulti
  rcases localMultiStep_strip_prefix_false (ι := ι) txnId prefixDb hMultiPrefixed with
    ⟨strippedLocalDb, hEq, hMulti'⟩
  have hPost :=
    h [] visibleDb
      ⟨finalCfg.cmd, strippedLocalDb, finalCfg.visibleDb⟩
      (by simp)
      hMulti'
      hSkip
  rcases hPost with ⟨hLocalEq, hVisibleEq⟩
  constructor
  · simpa [hEq, hLocalEq]
  · exact hVisibleEq

theorem localMultiStep_seq_split_false (txnId : TxnId)
    {left right : Command ι Database} {localDb visibleDb : Database}
    {finalCfg : LocalConfig ι}
    (h :
      LocalMultiStep (fun _ _ _ => False) txnId ι
        ⟨.seq left right, localDb, visibleDb⟩ finalCfg) :
    (∃ left' localDb',
        finalCfg = ⟨.seq left' right, localDb', visibleDb⟩ ∧
        LocalMultiStep (fun _ _ _ => False) txnId ι
          ⟨left, localDb, visibleDb⟩
          ⟨left', localDb', visibleDb⟩) ∨
      ∃ midLocalDb,
        LocalMultiStep (fun _ _ _ => False) txnId ι
          ⟨left, localDb, visibleDb⟩
          ⟨(Command.skip : Command ι Database), midLocalDb, visibleDb⟩ ∧
        LocalMultiStep (fun _ _ _ => False) txnId ι
          ⟨right, midLocalDb, visibleDb⟩
          finalCfg := by
  induction h with
  | refl =>
      left
      exact ⟨left, localDb, rfl, MultiStep.refl⟩
  | tail hPrev hLast ih =>
      rename_i cfg₂ cfg₃
      cases ih with
      | inl hPending =>
          rcases hPending with ⟨left', localDb', hCfg, hLeftMulti⟩
          cases hCfg
          cases cfg₃ with
          | mk cmd₃ localDb₃ visibleDb₃ =>
              cases hLast with
              | inl hLocal =>
                  rcases hLocal with ⟨hLocal, hVisibleEq⟩
                  subst hVisibleEq
                  cases hLocal with
                  | seqLeft hStep =>
                      left
                      exact ⟨_, _, rfl,
                        MultiStep.tail hLeftMulti
                          (localInterleavedStep_of_localStep (fun _ _ _ => False) txnId hStep)⟩
                  | seqSkip =>
                      right
                      exact ⟨localDb', hLeftMulti, MultiStep.refl⟩
              | inr hRely =>
                  exact False.elim hRely.2.2.2
      | inr hDone =>
          rcases hDone with ⟨midLocalDb, hLeftDone, hRightMulti⟩
          right
          exact ⟨midLocalDb, hLeftDone, MultiStep.tail hRightMulti hLast⟩

theorem localValid_seq_false (txnId : TxnId) (P P' Q : BiAssertion)
    (left right : Command ι Database)
    (hLeft : LocalValid (fun _ _ _ => False) txnId P left P')
    (hRight : LocalValid (fun _ _ _ => False) txnId P' right Q) :
    LocalValid (fun _ _ _ => False) txnId P (.seq left right) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  rcases localMultiStep_seq_split_false (ι := ι) txnId hMulti with hPending | hDone
  · rcases hPending with ⟨left', localDb', hEq, _hLeftMulti⟩
    cases hEq
    cases hSkip
  · rcases hDone with ⟨midLocalDb, hLeftMulti, hRightMulti⟩
    have hMid : P' midLocalDb visibleDb := by
      exact hLeft localDb visibleDb
        ⟨(Command.skip : Command ι Database), midLocalDb, visibleDb⟩
        hP
        hLeftMulti
        rfl
    exact hRight midLocalDb visibleDb finalCfg hMid hRightMulti hSkip

theorem localMultiStep_single (R : LocalRely) (txnId : TxnId)
    {cmd cmd' : Command ι Database} {localDb localDb' visibleDb : Database}
    (h : Semantics.LocalStep visibleDb txnId cmd localDb cmd' localDb') :
    LocalMultiStep R txnId ι
      ⟨cmd, localDb, visibleDb⟩
      ⟨cmd', localDb', visibleDb⟩ := by
  exact MultiStep.tail MultiStep.refl (localInterleavedStep_of_localStep R txnId h)

theorem globalMultiStep_single (R : Rely)
    {program program' : Semantics.Program} {db db' : Database}
    (h : Semantics.Step program db program' db') :
    GlobalMultiStep R
      ⟨program, db⟩
      ⟨program', db'⟩ := by
  exact MultiStep.tail MultiStep.refl (globalInterleavedStep_of_step R h)

theorem MultiStepFwd.snoc {step : α → α → Prop} {cfg₁ cfg₂ cfg₃ : α}
    (h₁₂ : MultiStepFwd step cfg₁ cfg₂) (h₂₃ : step cfg₂ cfg₃) :
    MultiStepFwd step cfg₁ cfg₃ := by
  induction h₁₂ with
  | refl =>
      exact MultiStepFwd.cons h₂₃ MultiStepFwd.refl
  | cons h₁₂ h₂₃ ih =>
      exact MultiStepFwd.cons h₁₂ (ih h₂₃)

theorem MultiStep.toFwd {step : α → α → Prop} {cfg₁ cfg₂ : α}
    (h : MultiStep step cfg₁ cfg₂) :
    MultiStepFwd step cfg₁ cfg₂ := by
  induction h with
  | refl =>
      exact MultiStepFwd.refl
  | tail hPrev hLast ih =>
      exact MultiStepFwd.snoc ih hLast

theorem globalValid_skip {I : Assertion} {R : Rely} {G : Guarantee}
    (hStable : stableAssertion R I) :
    GlobalValid I R (Command.skip : Semantics.Program) G I := by
  intro db hDb
  refine ⟨?_, ?_⟩
  · intro finalCfg hRun _hDone
    exact (skipGlobalFwd_preserves R I hStable (MultiStep.toFwd hRun) hDb).2
  · intro txnId midCfg nextProgram nextDb hRun hCommit
    have hProgram :
        midCfg.program = (Command.skip : Semantics.Program) :=
      (skipGlobalFwd_preserves R I hStable (MultiStep.toFwd hRun) hDb).1
    have hCommit' :
        TxnCommitStep txnId (Command.skip : Semantics.Program)
          midCfg.globalDb nextProgram nextDb := by
      simpa [hProgram] using hCommit
    cases hCommit'

theorem MultiStep.trans {step : α → α → Prop} {cfg₁ cfg₂ cfg₃ : α}
    (h₁₂ : MultiStep step cfg₁ cfg₂) (h₂₃ : MultiStep step cfg₂ cfg₃) :
    MultiStep step cfg₁ cfg₃ := by
  induction h₂₃ with
  | refl =>
      exact h₁₂
  | tail hPrev hLast ih =>
      exact MultiStep.tail ih hLast

theorem MultiStep.cons {step : α → α → Prop} {cfg₁ cfg₂ cfg₃ : α}
    (h₁₂ : step cfg₁ cfg₂) (h₂₃ : MultiStep step cfg₂ cfg₃) :
    MultiStep step cfg₁ cfg₃ := by
  exact MultiStep.trans (MultiStep.tail MultiStep.refl h₁₂) h₂₃

theorem MultiStep.ofFwd {step : α → α → Prop} {cfg₁ cfg₂ : α}
    (h : MultiStepFwd step cfg₁ cfg₂) :
    MultiStep step cfg₁ cfg₂ := by
  induction h with
  | refl =>
      exact MultiStep.refl
  | cons hFirst hRest ih =>
      exact MultiStep.cons hFirst ih

theorem MultiStep.head {step : α → α → Prop} {cfg₁ cfg₂ : α}
    (h : MultiStep step cfg₁ cfg₂) :
    cfg₁ = cfg₂ ∨ ∃ cfg', step cfg₁ cfg' ∧ MultiStep step cfg' cfg₂ := by
  induction h with
  | refl =>
      exact Or.inl rfl
  | tail hPrev hLast ih =>
      cases ih with
      | inl hEq =>
          subst hEq
          exact Or.inr ⟨_, hLast, MultiStep.refl⟩
      | inr hHead =>
          rcases hHead with ⟨cfg', hStep, hRest⟩
          exact Or.inr ⟨cfg', hStep, MultiStep.tail hRest hLast⟩

theorem no_localStep_from_skip (txnId : TxnId)
    {localDb visibleDb localDb' : Database} {cmd' : Command ι Database} :
    ¬ Semantics.LocalStep visibleDb txnId (Command.skip : Command ι Database) localDb cmd' localDb' := by
  intro h
  cases h

theorem no_localInterleavedStep_false_from_skip (txnId : TxnId)
    {localDb visibleDb : Database} {cfg' : LocalConfig ι} :
    ¬ localInterleavedStep (fun _ _ _ => False) txnId
        ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ cfg' := by
  intro h
  cases h with
  | inl hLocal =>
      exact no_localStep_from_skip txnId hLocal.1
  | inr hRely =>
      exact hRely.2.2.2

theorem no_localInterleavedStep_from_skip (R : LocalRely) (txnId : TxnId)
    {localDb visibleDb : Database} {cfg' : LocalConfig ι} :
    ¬ localInterleavedStep R txnId
        ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ cfg' := by
  intro h
  cases h with
  | inl hLocal =>
      exact no_localStep_from_skip txnId hLocal.1
  | inr hRely =>
      exact hRely.2.2.1 rfl

theorem localMultiStep_false_from_skip (txnId : TxnId)
    {localDb visibleDb : Database} {finalCfg : LocalConfig ι}
    (h : LocalMultiStep (fun _ _ _ => False) txnId ι
      ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ finalCfg) :
    finalCfg = ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ := by
  induction h with
  | refl =>
      rfl
  | tail hPrev hLast ih =>
      cases ih
      exfalso
      exact no_localInterleavedStep_false_from_skip txnId hLast

theorem localMultiStep_from_skip (R : LocalRely) (txnId : TxnId)
    {localDb visibleDb : Database} {finalCfg : LocalConfig ι}
    (h : LocalMultiStep R txnId ι
      ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ finalCfg) :
    finalCfg = ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩ := by
  induction h with
  | refl =>
      rfl
  | tail hPrev hLast ih =>
      cases ih
      exfalso
      exact no_localInterleavedStep_from_skip R txnId hLast

theorem localValid_skip (R : LocalRely) (txnId : TxnId) (P : BiAssertion) :
    LocalValid R txnId P (Command.skip : Command ι Database) P := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hEq := localMultiStep_from_skip (ι := ι) R txnId hMulti
  cases hEq
  simpa using hP

theorem localValid_conseq {R : LocalRely} {txnId : TxnId}
    {P P' Q Q' : BiAssertion} {c : Command ι Database}
    (hPre : ∀ localDb visibleDb, P localDb visibleDb → P' localDb visibleDb)
    (hValid : LocalValid R txnId P' c Q')
    (hPost : ∀ localDb visibleDb, Q' localDb visibleDb → Q localDb visibleDb) :
    LocalValid R txnId P c Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  exact hPost _ _ (hValid localDb visibleDb finalCfg (hPre _ _ hP) hMulti hSkip)

theorem localInterleavedStep_let_inv {R : LocalRely} {txnId : TxnId}
    {x : VarName} {expr : Expr} {body : Command ι Database}
    {localDb visibleDb : Database} {cfg : LocalConfig ι}
    (h :
      localInterleavedStep (ι := ι) R txnId
        ⟨(.letE x expr body : Command ι Database), localDb, visibleDb⟩ cfg) :
    (∃ value,
        Expr.eval expr = some value ∧
        cfg = ⟨Command.subst x value.toExpr body, localDb, visibleDb⟩) ∨
      ∃ visibleDb',
        cfg = ⟨(.letE x expr body : Command ι Database), localDb, visibleDb'⟩ ∧
        R localDb visibleDb visibleDb' := by
  cases cfg with
  | mk cmd' localDb' visibleDb' =>
      cases h with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          cases hLocal with
          | letE hEval =>
              subst hVisibleEq
              exact Or.inl ⟨_, hEval, rfl⟩
      | inr hRely =>
          rcases hRely with ⟨hCmd, hLocal, _hNotSkip, hR⟩
          subst hCmd
          subst hLocal
          exact Or.inr ⟨_, rfl, hR⟩

theorem localValid_let (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (x : VarName) (expr : Expr) (body : Command ι Database) (value : Value)
    (hStable : stableBiAssertion R P)
    (hEval : Expr.eval expr = some value)
    (hBody : LocalValid R txnId P (Command.subst x value.toExpr body) Q) :
    LocalValid R txnId P (.letE x expr body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.letE x expr body : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | cons hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        rcases localInterleavedStep_let_inv (txnId := txnId) (x := x) (expr := expr)
          (body := body) (localDb := localDb) (visibleDb := visibleDb) hStep with
          hLocal | hRely
        · rcases hLocal with ⟨steppedValue, hEvalStep, hEq⟩
          have hValueEq : steppedValue = value := by
            apply Option.some.inj
            rw [← hEvalStep, hEval]
          subst hValueEq
          subst hEq
          exact hBody localDb visibleDb _ hPvisible (MultiStep.ofFwd hRest) hCfgSkip
        · rcases hRely with ⟨visibleDb', hEq, hR⟩
          exact ih visibleDb' hEq (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_seq (R : LocalRely) (txnId : TxnId) (P P' Q : BiAssertion)
    (left right : Command ι Database)
    (hLeft : LocalValid R txnId P left P')
    (hStableMid : stableBiAssertion R P')
    (hRight : LocalValid R txnId P' right Q) :
    LocalValid R txnId P (.seq left right) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hReady :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ readyLocalDb readyVisibleDb,
          cfg₁ = ⟨(.seq .skip right : Command ι Database), readyLocalDb, readyVisibleDb⟩ →
          P' readyLocalDb readyVisibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro readyLocalDb readyVisibleDb hStart hReadyPre hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro readyLocalDb readyVisibleDb hStart hReadyPre hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | seqLeft hStepLeft =>
                    exact False.elim (no_localStep_from_skip txnId hStepLeft)
                | seqSkip =>
                    exact hRight readyLocalDb visibleDbMid _ hReadyPre
                      (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih localDbMid visibleDbMid rfl
                  (hStableMid _ _ _ hReadyPre hR) hCfgSkip
  have hPending :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ left' currentLocalDb currentVisibleDb,
          cfg₁ = ⟨(.seq left' right : Command ι Database), currentLocalDb, currentVisibleDb⟩ →
          left' ≠ (Command.skip : Command ι Database) →
          LocalMultiStep R txnId ι
            ⟨left, localDb, visibleDb⟩
            ⟨left', currentLocalDb, currentVisibleDb⟩ →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro left' currentLocalDb currentVisibleDb hStart hNotSkip _hLeftPath hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro left' currentLocalDb currentVisibleDb hStart hNotSkip hLeftPath hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | seqLeft hStepLeft =>
                    rename_i steppedLeft
                    have hLeftPath' :
                        LocalMultiStep R txnId ι
                          ({ cmd := left, localDb := localDb, visibleDb := visibleDb })
                          ({ cmd := steppedLeft, localDb := localDbMid, visibleDb := visibleDbMid }) := by
                      exact MultiStep.tail hLeftPath
                        (localInterleavedStep_of_localStep R txnId hStepLeft)
                    by_cases hCmdMidSkip : steppedLeft = (Command.skip : Command ι Database)
                    · have hMid : P' localDbMid visibleDbMid := by
                        exact hLeft localDb visibleDb
                          { cmd := steppedLeft, localDb := localDbMid, visibleDb := visibleDbMid }
                          hP
                          hLeftPath'
                          hCmdMidSkip
                      subst hCmdMidSkip
                      exact hReady hRest localDbMid visibleDbMid rfl hMid hCfgSkip
                    · exact ih steppedLeft localDbMid visibleDbMid rfl hCmdMidSkip hLeftPath' hCfgSkip
                | seqSkip =>
                    exact False.elim (hNotSkip rfl)
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hSeqNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                have hLeftPath' :
                    LocalMultiStep R txnId ι
                      ({ cmd := left, localDb := localDb, visibleDb := visibleDb })
                      ({ cmd := left', localDb := localDbMid, visibleDb := visibleDbMid }) := by
                  exact MultiStep.tail hLeftPath
                    (Or.inr ⟨rfl, rfl, hNotSkip, hR⟩)
                exact ih left' localDbMid visibleDbMid rfl hNotSkip hLeftPath' hCfgSkip
  by_cases hLeftSkip : left = (Command.skip : Command ι Database)
  · subst hLeftSkip
    have hMid : P' localDb visibleDb := by
      exact hLeft localDb visibleDb
        ⟨(Command.skip : Command ι Database), localDb, visibleDb⟩
        hP
        MultiStep.refl
        rfl
    exact hReady (MultiStep.toFwd hMulti) localDb visibleDb rfl hMid hSkip
  · exact hPending (MultiStep.toFwd hMulti) left localDb visibleDb rfl hLeftSkip MultiStep.refl hSkip

theorem localValid_ite (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (cond : Expr) (thenBranch elseBranch : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hThen :
      Expr.eval cond = some (.scalar (.bool true)) →
      LocalValid R txnId P thenBranch Q)
    (hElse :
      Expr.eval cond = some (.scalar (.bool false)) →
      LocalValid R txnId P elseBranch Q) :
    LocalValid R txnId P (.ite cond thenBranch elseBranch) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.ite cond thenBranch elseBranch : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | iteTrue hEvalTrue =>
                    exact hThen hEvalTrue localDb visibleDbMid _ hPvisible
                      (MultiStep.ofFwd hRest) hCfgSkip
                | iteFalse hEvalFalse =>
                    exact hElse hEvalFalse localDb visibleDbMid _ hPvisible
                      (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_select (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (binder source : VarName) (predicate : Expr) (body : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hBody :
      ∀ localDb visibleDb selected,
        P localDb visibleDb →
        Semantics.collectSelected visibleDb source predicate = some selected →
        LocalValid R txnId P
          (Command.subst binder (.lit (.set selected)) body) Q) :
    LocalValid R txnId P (.select binder source predicate body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.select binder source predicate body : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | select hSelect =>
                    exact hBody localDb visibleDbMid _ hPvisible hSelect
                      localDb visibleDbMid _ hPvisible (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_insert {ι : Type} (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (expr : Expr)
    (hStable : stableBiAssertion R P)
    (hPost :
      ∀ localDb visibleDb record,
        P localDb visibleDb →
        Expr.eval expr = some (.record record) →
        Semantics.insertFresh visibleDb localDb record →
        Q (localDb ++ [Row.fromInsert txnId record]) visibleDb) :
    LocalValid R txnId P (.insert expr : Command ι Database) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.insert expr : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | insert hEval hFresh =>
                    have hEq := localMultiStep_from_skip (ι := ι) R txnId (MultiStep.ofFwd hRest)
                    cases hEq
                    simpa using hPost localDb visibleDbMid _ hPvisible hEval hFresh
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_delete {ι : Type} (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (source : VarName) (predicate : Expr)
    (hStable : stableBiAssertion R P)
    (hPost :
      ∀ localDb visibleDb removed,
        P localDb visibleDb →
        Semantics.collectDeleted visibleDb txnId source predicate = some removed →
        Database.disjointIds localDb removed →
        Q (localDb ++ removed) visibleDb) :
    LocalValid R txnId P (.delete source predicate : Command ι Database) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.delete source predicate : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | delete hDelete hDisjoint =>
                    have hEq := localMultiStep_from_skip (ι := ι) R txnId (MultiStep.ofFwd hRest)
                    cases hEq
                    simpa using hPost localDb visibleDbMid _ hPvisible hDelete hDisjoint
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_update {ι : Type} (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (source : VarName) (updateExpr predicate : Expr)
    (hStable : stableBiAssertion R P)
    (hPost :
      ∀ localDb visibleDb updated,
        P localDb visibleDb →
        Semantics.collectUpdated visibleDb txnId source updateExpr predicate = some updated →
        Database.disjointIds localDb updated →
        Q (localDb ++ updated) visibleDb) :
    LocalValid R txnId P (.update source updateExpr predicate : Command ι Database) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.update source updateExpr predicate : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | update hUpdate hDisjoint =>
                    have hEq := localMultiStep_from_skip (ι := ι) R txnId (MultiStep.ofFwd hRest)
                    cases hEq
                    simpa using hPost localDb visibleDbMid _ hPvisible hUpdate hDisjoint
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_foreach (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (source : Expr) (doneVar elemVar : VarName) (body : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hBody :
      ∀ records,
        Expr.eval source = some (.set records) →
        LocalValid R txnId P
          (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body) Q) :
    LocalValid R txnId P (.foreach source doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.foreach source doneVar elemVar body : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | foreachStart hEval =>
                    exact hBody _ hEval localDb visibleDbMid _ hPvisible
                      (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_foreachStart (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (source : Expr) (records : SetLit) (doneVar elemVar : VarName) (body : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hEval : Expr.eval source = some (.set records))
    (hBody :
      LocalValid R txnId P
        (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body) Q) :
    LocalValid R txnId P (.foreach source doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ = ⟨(.foreach source doneVar elemVar body : Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | foreachStart hEvalStep =>
                    rename_i steppedRecords
                    have hEvalEq : some (.set steppedRecords : Value) = some (.set records : Value) := by
                      calc
                        some (.set steppedRecords : Value) = source.eval := by simp [hEvalStep]
                        _ = some (.set records : Value) := hEval
                    have hRecords : steppedRecords = records := by
                      injection hEvalEq with hValue
                      injection hValue
                    subst hRecords
                    exact hBody localDb visibleDbMid _ hPvisible
                      (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_foreachDone (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (done : SetLit) (doneVar elemVar : VarName) (body : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hPost : ∀ localDb visibleDb, P localDb visibleDb → Q localDb visibleDb) :
    LocalValid R txnId P
      (.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ =
            ⟨(.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body : Command ι Database),
              localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | foreachDone =>
                    have hEq := localMultiStep_from_skip (ι := ι) R txnId (MultiStep.ofFwd hRest)
                    cases hEq
                    simpa using hPost localDb visibleDbMid hPvisible
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_foreachNext (R : LocalRely) (txnId : TxnId) (P Q : BiAssertion)
    (done : SetLit) (current : RecordLit) (rest : SetLit)
    (doneVar elemVar : VarName) (body : Command ι Database)
    (hStable : stableBiAssertion R P)
    (hSeq :
      LocalValid R txnId P
        (.seq
          (Command.subst doneVar (Expr.setLit done)
            (Command.subst elemVar (.lit (.record current)) body))
          (.foreachRuntime
            (Expr.setLit (done ++ [current]))
            (Expr.setLit rest)
            doneVar
            elemVar
            body))
        Q) :
    LocalValid R txnId P
      (.foreachRuntime (Expr.setLit done) (Expr.setLit (current :: rest)) doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hAux :
      ∀ {cfg₁ cfg₂ : LocalConfig ι},
        MultiStepFwd (localInterleavedStep (ι := ι) R txnId) cfg₁ cfg₂ →
        ∀ visibleDb,
          cfg₁ =
            ⟨(.foreachRuntime (Expr.setLit done) (Expr.setLit (current :: rest)) doneVar elemVar body :
                Command ι Database), localDb, visibleDb⟩ →
          P localDb visibleDb →
          cfg₂.cmd = (Command.skip : Command ι Database) →
          Q cfg₂.localDb cfg₂.visibleDb := by
    intro cfg₁ cfg₂ hPath
    induction hPath with
    | refl =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases hCfgSkip
    | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
        intro visibleDb hStart hPvisible hCfgSkip
        cases hStart
        cases cfgMid with
        | mk cmdMid localDbMid visibleDbMid =>
            cases hStep with
            | inl hLocal =>
                rcases hLocal with ⟨hLocal, hVisibleEq⟩
                subst hVisibleEq
                cases hLocal with
                | foreachNext =>
                    exact hSeq localDb visibleDbMid _ hPvisible
                      (MultiStep.ofFwd hRest) hCfgSkip
            | inr hRely =>
                rcases hRely with ⟨hCmd, hLocalEq, _hNotSkip, hR⟩
                subst hCmd
                subst hLocalEq
                exact ih visibleDbMid rfl (hStable _ _ _ hPvisible hR) hCfgSkip
  exact hAux (MultiStep.toFwd hMulti) visibleDb rfl hP hSkip

theorem localValid_skip_false (txnId : TxnId) (P : BiAssertion) :
    LocalValid (fun _ _ _ => False) txnId P (Command.skip : Command ι Database) P := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hEq := localMultiStep_false_from_skip (ι := ι) txnId hMulti
  cases hEq
  simpa using hP

theorem localValid_let_false (txnId : TxnId) (P Q : BiAssertion)
    (x : VarName) (expr : Expr) (body : Command ι Database) (value : Value)
    (hEval : Expr.eval expr = some value)
    (hBody : LocalValid (fun _ _ _ => False) txnId P (Command.subst x value.toExpr body) Q) :
    LocalValid (fun _ _ _ => False) txnId P (.letE x expr body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | letE hEvalStep =>
              rename_i steppedValue
              have hSome : some steppedValue = some value := by
                rw [← hEvalStep, hEval]
              have hValue : steppedValue = value := Option.some.inj hSome
              subst hValue
              simpa using hBody localDb visibleDb' finalCfg hP hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_ite_false (txnId : TxnId) (P Q : BiAssertion)
    (cond : Expr) (thenBranch elseBranch : Command ι Database)
    (hThen :
      Expr.eval cond = some (.scalar (.bool true)) →
      LocalValid (fun _ _ _ => False) txnId P thenBranch Q)
    (hElse :
      Expr.eval cond = some (.scalar (.bool false)) →
      LocalValid (fun _ _ _ => False) txnId P elseBranch Q) :
    LocalValid (fun _ _ _ => False) txnId P (.ite cond thenBranch elseBranch) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | iteTrue hEvalTrue =>
              exact hThen hEvalTrue localDb visibleDb' finalCfg hP hRest hSkip
          | iteFalse hEvalFalse =>
              exact hElse hEvalFalse localDb visibleDb' finalCfg hP hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_select_false (txnId : TxnId) (P Q : BiAssertion)
    (binder source : VarName) (predicate : Expr) (body : Command ι Database)
    (hBody :
      ∀ localDb visibleDb selected,
        P localDb visibleDb →
        Semantics.collectSelected visibleDb source predicate = some selected →
        LocalValid (fun _ _ _ => False) txnId P
          (Command.subst binder (.lit (.set selected)) body) Q) :
    LocalValid (fun _ _ _ => False) txnId P (.select binder source predicate body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | select hSelect =>
              have hBodyValid := hBody localDb visibleDb' _ hP hSelect
              simpa using hBodyValid localDb visibleDb' finalCfg hP hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

/-- Variant of `localValid_select_false` whose body hypothesis exposes the
ambient `visibleDb` to the body's `LocalValid` precondition: the body proof
can leverage `vd = visibleDb` and any side info bound to that specific
visibleDb (e.g. the outer `collectSelected visibleDb ...` witness). The
strengthening goes through because the wrapper's outer step pins
`visibleDb' = visibleDb` under False rely, so when we invoke the body
LocalValid we always have `vd = visibleDb` available. -/
theorem localValid_select_false_pinVd (txnId : TxnId) (P Q : BiAssertion)
    (binder source : VarName) (predicate : Expr) (body : Command ι Database)
    (hBody :
      ∀ localDb visibleDb selected,
        P localDb visibleDb →
        Semantics.collectSelected visibleDb source predicate = some selected →
        LocalValid (fun _ _ _ => False) txnId
          (fun ld vd => P ld vd ∧ vd = visibleDb)
          (Command.subst binder (.lit (.set selected)) body) Q) :
    LocalValid (fun _ _ _ => False) txnId P (.select binder source predicate body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | select hSelect =>
              have hBodyValid :=
                hBody localDb visibleDb' _ hP hSelect
              exact hBodyValid localDb visibleDb' finalCfg ⟨hP, rfl⟩ hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_insert_false {ι : Type} (txnId : TxnId) (P Q : BiAssertion)
    (expr : Expr)
    (hPost :
      ∀ localDb visibleDb record,
        P localDb visibleDb →
        Expr.eval expr = some (.record record) →
        Semantics.insertFresh visibleDb localDb record →
        Q (localDb ++ [Row.fromInsert txnId record]) visibleDb) :
    LocalValid (fun _ _ _ => False) txnId P ((.insert expr : Command ι Database)) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | insert hEval hFresh =>
              have hEq := localMultiStep_false_from_skip (ι := ι) txnId hRest
              cases hEq
              simpa using hPost localDb visibleDb' _ hP hEval hFresh
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_delete_false {ι : Type} (txnId : TxnId) (P Q : BiAssertion)
    (source : VarName) (predicate : Expr)
    (hPost :
      ∀ localDb visibleDb removed,
        P localDb visibleDb →
        Semantics.collectDeleted visibleDb txnId source predicate = some removed →
        Database.disjointIds localDb removed →
        Q (localDb ++ removed) visibleDb) :
    LocalValid (fun _ _ _ => False) txnId P ((.delete source predicate : Command ι Database)) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | delete hDelete hDisjoint =>
              have hEq := localMultiStep_false_from_skip (ι := ι) txnId hRest
              cases hEq
              simpa using hPost localDb visibleDb' _ hP hDelete hDisjoint
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_update_false {ι : Type} (txnId : TxnId) (P Q : BiAssertion)
    (source : VarName) (updateExpr predicate : Expr)
    (hPost :
      ∀ localDb visibleDb updated,
        P localDb visibleDb →
        Semantics.collectUpdated visibleDb txnId source updateExpr predicate = some updated →
        Database.disjointIds localDb updated →
        Q (localDb ++ updated) visibleDb) :
    LocalValid (fun _ _ _ => False) txnId P
      ((.update source updateExpr predicate : Command ι Database)) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | update hUpdate hDisjoint =>
              have hEq := localMultiStep_false_from_skip (ι := ι) txnId hRest
              cases hEq
              simpa using hPost localDb visibleDb' _ hP hUpdate hDisjoint
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_foreachStart_false (txnId : TxnId) (P Q : BiAssertion)
    (source : Expr) (records : SetLit) (doneVar elemVar : VarName) (body : Command ι Database)
    (hEval : Expr.eval source = some (.set records))
    (hBody :
      LocalValid (fun _ _ _ => False) txnId P
        (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body) Q) :
    LocalValid (fun _ _ _ => False) txnId P (.foreach source doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | foreachStart hEvalStep =>
              rename_i steppedRecords
              have hEvalEq : some (.set steppedRecords : Value) = some (.set records : Value) := by
                calc
                  some (.set steppedRecords : Value) = source.eval := by simp [hEvalStep]
                  _ = some (.set records : Value) := hEval
              have hRecords : steppedRecords = records := by
                injection hEvalEq with hValue
                injection hValue
              subst hRecords
              simpa using hBody localDb visibleDb' finalCfg hP hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_foreachDone_false (txnId : TxnId) (P Q : BiAssertion)
    (done : SetLit) (doneVar elemVar : VarName) (body : Command ι Database)
    (hPost : ∀ localDb visibleDb, P localDb visibleDb → Q localDb visibleDb) :
    LocalValid (fun _ _ _ => False) txnId P
      (.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | foreachDone =>
              have hEq := localMultiStep_false_from_skip (ι := ι) txnId hRest
              cases hEq
              simpa using hPost localDb visibleDb' hP
      | inr hRely =>
          exact False.elim hRely.2.2.2

theorem localValid_foreachNext_false (txnId : TxnId) (P Q : BiAssertion)
    (done : SetLit) (current : RecordLit) (rest : SetLit)
    (doneVar elemVar : VarName) (body : Command ι Database)
    (hSeq :
      LocalValid (fun _ _ _ => False) txnId P
        (.seq
          (Command.subst doneVar (Expr.setLit done)
            (Command.subst elemVar (.lit (.record current)) body))
          (.foreachRuntime
            (Expr.setLit (done ++ [current]))
            (Expr.setLit rest)
            doneVar
            elemVar
            body))
        Q) :
    LocalValid (fun _ _ _ => False) txnId P
      (.foreachRuntime (Expr.setLit done) (Expr.setLit (current :: rest)) doneVar elemVar body) Q := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  have hHead := MultiStep.head hMulti
  cases hHead with
  | inl hEq =>
      cases hEq
      cases hSkip
  | inr hHead =>
      rcases hHead with ⟨⟨cmd', localDb', visibleDb'⟩, hStep, hRest⟩
      cases hStep with
      | inl hLocal =>
          rcases hLocal with ⟨hLocal, hVisibleEq⟩
          subst hVisibleEq
          cases hLocal with
          | foreachNext =>
              simpa using hSeq localDb visibleDb' finalCfg hP hRest hSkip
      | inr hRely =>
          exact False.elim hRely.2.2.2

/-- Inductive local proof system corresponding to the paper's Sec. 4 rules. The soundness theorem
below shows that derivations in `LocalRG` imply `LocalValid`. -/
inductive LocalRG (R : LocalRely) (txnId : TxnId) :
    BiAssertion → Command ι Database → BiAssertion → Prop where
  | skip {P} :
      stableBiAssertion R P →
      LocalRG R txnId P .skip P
  | letE {P Q x expr body value} :
      stableBiAssertion R P →
      Expr.eval expr = some value →
      LocalRG R txnId P (Command.subst x value.toExpr body) Q →
      LocalRG R txnId P (.letE x expr body) Q
  | ite {P Q cond thenBranch elseBranch} :
      stableBiAssertion R P →
      (Expr.eval cond = some (.scalar (.bool true)) → LocalRG R txnId P thenBranch Q) →
      (Expr.eval cond = some (.scalar (.bool false)) → LocalRG R txnId P elseBranch Q) →
      LocalRG R txnId P (.ite cond thenBranch elseBranch) Q
  | seq {P P' Q left right} :
      stableBiAssertion R P →
      LocalRG R txnId P left P' →
      LocalRG R txnId P' right Q →
      LocalRG R txnId P (.seq left right) Q
  | select {P Q binder source predicate body} :
      stableBiAssertion R P →
      (∀ localDb visibleDb selected,
        P localDb visibleDb →
        Semantics.collectSelected visibleDb source predicate = some selected →
        LocalRG R txnId P (Command.subst binder (.lit (.set selected)) body) Q) →
      LocalRG R txnId P (.select binder source predicate body) Q
  | insert {P Q expr} :
      stableBiAssertion R P →
      (∀ localDb visibleDb record,
        P localDb visibleDb →
        Expr.eval expr = some (.record record) →
        Semantics.insertFresh visibleDb localDb record →
        Q (localDb ++ [Row.fromInsert txnId record]) visibleDb) →
      LocalRG R txnId P (.insert expr) Q
  | delete {P Q source predicate} :
      stableBiAssertion R P →
      (∀ localDb visibleDb removed,
        P localDb visibleDb →
        Semantics.collectDeleted visibleDb txnId source predicate = some removed →
        Database.disjointIds localDb removed →
        Q (localDb ++ removed) visibleDb) →
      LocalRG R txnId P (.delete source predicate) Q
  | update {P Q source updateExpr predicate} :
      stableBiAssertion R P →
      (∀ localDb visibleDb updated,
        P localDb visibleDb →
        Semantics.collectUpdated visibleDb txnId source updateExpr predicate = some updated →
        Database.disjointIds localDb updated →
        Q (localDb ++ updated) visibleDb) →
      LocalRG R txnId P (.update source updateExpr predicate) Q
  | foreach {P Q source doneVar elemVar body} :
      stableBiAssertion R P →
      (∀ records,
        Expr.eval source = some (.set records) →
          LocalRG R txnId P (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body) Q) →
      LocalRG R txnId P (.foreach source doneVar elemVar body) Q
  | conseq {P P' Q Q' c} :
      stableBiAssertion R P →
      (∀ localDb visibleDb, P localDb visibleDb → P' localDb visibleDb) →
      LocalRG R txnId P' c Q' →
      (∀ localDb visibleDb, Q' localDb visibleDb → Q localDb visibleDb) →
      LocalRG R txnId P c Q

/-- Inductive top-level proof system. The `par` rule is the paper-style RG composition rule over
the canonical interleaving semantics. -/
inductive GlobalRG :
    Rely → Assertion → Semantics.Program → Guarantee → Assertion → Prop where
  | txn {I isolation txnId body P Q G} :
      stableAssertion R I →
      stableIsolation R isolation.exec →
      stableIsolation R isolation.commit →
      (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb) →
      LocalRG (relyMod R isolation.exec) txnId P body Q →
      stableBiAssertion (relyMod R isolation.commit) Q →
      (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
      (∀ db db', I db → G db db' → I db') →
      GlobalRG R I (.txn txnId isolation body) G I
  | par {I left right Gleft Gright} :
      GlobalRG (fun db db' => R db db' ∨ Gright db db') I left Gleft I →
      GlobalRG (fun db db' => R db db' ∨ Gleft db db') I right Gright I →
      GlobalRG R I (.par left right) (fun db db' => Gleft db db' ∨ Gright db db') I
  | conseq {I I' program G G'} :
      GlobalRG R I program G I →
      (∀ db, I' db → I db) →
      stableAssertion R I' →
      (∀ db db', G db db' → G' db db') →
      (∀ db db', I db → G' db db' → I db') →
      GlobalRG R I' program G' I

theorem localRG_stablePre {R : LocalRely} {txnId : TxnId}
    {P : BiAssertion} {c : Command ι Database} {Q : BiAssertion}
    (h : LocalRG R txnId P c Q) :
    stableBiAssertion R P := by
  induction h with
  | skip hStable =>
      exact hStable
  | letE hStable _ _ =>
      exact hStable
  | ite hStable _ _ =>
      exact hStable
  | seq hStable _ _ _ _ =>
      exact hStable
  | select hStable _ =>
      exact hStable
  | insert hStable _ =>
      exact hStable
  | delete hStable _ =>
      exact hStable
  | update hStable _ =>
      exact hStable
  | foreach hStable _ =>
      exact hStable
  | conseq hStable _ _ _ =>
      exact hStable

theorem localRG_sound {R : LocalRely} {txnId : TxnId}
    {P : BiAssertion} {c : Command ι Database} {Q : BiAssertion}
    (h : LocalRG R txnId P c Q) :
    LocalValid R txnId P c Q := by
  induction h with
  | skip hStable =>
      simpa using (localValid_skip R txnId _)
  | letE hStable hEval hBody ih =>
      simpa using (localValid_let R txnId _ _ _ _ _ _ hStable hEval ih)
  | ite hStable hThen hElse ihThen ihElse =>
      simpa using (localValid_ite R txnId _ _ _ _ _ hStable ihThen ihElse)
  | seq hStable hLeft hRight ihLeft ihRight =>
      simpa using
        (localValid_seq R txnId _ _ _ _ _ ihLeft (localRG_stablePre hRight) ihRight)
  | select hStable hBody ih =>
      simpa using (localValid_select R txnId _ _ _ _ _ _ hStable ih)
  | insert hStable hPost =>
      simpa using (localValid_insert R txnId _ _ _ hStable hPost)
  | delete hStable hPost =>
      simpa using (localValid_delete R txnId _ _ _ _ hStable hPost)
  | update hStable hPost =>
      simpa using (localValid_update R txnId _ _ _ _ _ hStable hPost)
  | foreach hStable hBody ih =>
      simpa using (localValid_foreach R txnId _ _ _ _ _ _ hStable ih)
  | conseq hStable hPre hRG hPost ih =>
      exact localValid_conseq hPre ih hPost

/-- Endpoints relevant to `RG-Txn`: either the transaction has already committed, or it is poised to
commit from a runtime `skip` state. -/
def ReadyToFinish : GlobalConfig → Prop
  | ⟨program, currentDb⟩ =>
      program = (Command.skip : Semantics.Program) ∨
        ∃ txnId isolation localDb snapshot,
          program = (.txnRuntime txnId isolation localDb snapshot (Command.skip : Semantics.Program)
            : Semantics.Program) ∧
          isolation.commit localDb snapshot currentDb

theorem execIsolation_of_future_ready {R : Rely} {txnId : TxnId}
    {isolation : IsolationSpec Database}
    (hExecStable : stableIsolation R isolation.exec)
    {cfg₁ cfg₂ : GlobalConfig}
    (hPath : MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂) :
    ∀ localDb snapshot currentDb currentBody,
      MultiStep R snapshot currentDb →
      cfg₁ = ⟨(.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program), currentDb⟩ →
      currentBody ≠ (Command.skip : Semantics.Program) →
      ReadyToFinish cfg₂ →
      isolation.exec localDb snapshot currentDb := by
  intro localDb snapshot currentDb currentBody hReachSnap hStart hNotSkip hReady
  induction hPath generalizing localDb snapshot currentDb currentBody with
  | refl =>
      cases hStart
      rcases hReady with hSkip | ⟨_txnId', _isolation', localDb', snapshot', hProgram, _⟩
      · cases hSkip
      · have hBodySkip : currentBody = (Command.skip : Semantics.Program) := by
          injection hProgram
        exact False.elim (hNotSkip hBodySkip)
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txnRuntime_inv_full (by simpa using hActual) with
            ⟨_, _, _, _, _, hExec, _⟩ | hCommit
          ·
              exact hExec
          ·
              exact False.elim (hNotSkip hCommit.1)
      | inr hRely =>
          rcases hRely with ⟨hProgram, hR⟩
          cases cfgMid with
          | mk programMid dbMid =>
              have hMidProgram :
                  programMid =
                    (.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program) := by
                simpa using hProgram
              subst hMidProgram
              have hReachSnap' : MultiStep R snapshot dbMid := MultiStep.tail hReachSnap hR
              have hMid :
                  isolation.exec localDb snapshot dbMid := by
                exact ih localDb snapshot dbMid currentBody hReachSnap' rfl hNotSkip hReady
              exact (hExecStable _ _ _ _ hReachSnap hMid hR).1

theorem commitIsolation_of_future_ready {R : Rely} {txnId : TxnId}
    {isolation : IsolationSpec Database}
    (hCommitStable : stableIsolation R isolation.commit)
    {cfg₁ cfg₂ : GlobalConfig}
    (hPath : MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂) :
    ∀ localDb snapshot currentDb,
      MultiStep R snapshot currentDb →
      cfg₁ = ⟨(.txnRuntime txnId isolation localDb snapshot (Command.skip : Semantics.Program)
        : Semantics.Program), currentDb⟩ →
      ReadyToFinish cfg₂ →
      isolation.commit localDb snapshot currentDb := by
  intro localDb snapshot currentDb hReachSnap hStart hReady
  induction hPath generalizing localDb snapshot currentDb with
  | refl =>
      cases hStart
      rcases hReady with hSkip | ⟨txnId', isolation', localDb', snapshot', hProgram, hCommit⟩
      · cases hSkip
      · injection hProgram with hTxnId hIso hLocal hSnapshot
        subst hTxnId hIso hLocal hSnapshot
        simpa using hCommit
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txnRuntime_inv_full (by simpa using hActual) with
            ⟨_, _, hNotSkip, _, _, _, _⟩ | hCommit
          · exact False.elim (hNotSkip rfl)
          · simpa using hCommit.2.2.2
      | inr hRely =>
          rcases hRely with ⟨hProgram, hR⟩
          cases cfgMid with
          | mk programMid dbMid =>
              have hMidProgram :
                  programMid =
                    (.txnRuntime txnId isolation localDb snapshot (Command.skip : Semantics.Program)
                      : Semantics.Program) := by
                simpa using hProgram
              subst hMidProgram
              have hReachSnap' : MultiStep R snapshot dbMid := MultiStep.tail hReachSnap hR
              have hMid :
                  isolation.commit localDb snapshot dbMid := by
                exact ih localDb snapshot dbMid hReachSnap' rfl hReady
              exact (hCommitStable _ _ _ _ hReachSnap hMid hR).1

theorem txnRuntimeFwd_sound {R : Rely} {txnId : TxnId}
    {I : Assertion} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee}
    (hStableI : stableAssertion R I)
    (hExecStable : stableIsolation R isolation.exec)
    (hPre : ∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb)
    (hBody : LocalValid (relyMod R isolation.exec) txnId P body Q)
    (hQStable : stableBiAssertion (relyMod R isolation.commit) Q)
    (hCommitStable : stableIsolation R isolation.commit)
    (hGuarantee : ∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb))
    (hPreserve : ∀ db db', I db → G db db' → I db')
    {startDb : Database} (hStartI : I startDb) :
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ localDb snapshot currentDb currentBody,
        MultiStep R snapshot currentDb →
        cfg₁ =
          ⟨(.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program), currentDb⟩ →
        ReadyToFinish cfg₂ →
        I currentDb →
        (if currentBody = (Command.skip : Semantics.Program) then
           Q localDb currentDb
         else
           LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
             ⟨body, [], startDb⟩
             ⟨currentBody, localDb, currentDb⟩) →
        match cfg₂.program with
        | .txnRuntime _ _ localDb' _ body' =>
            I cfg₂.globalDb ∧
              (if body' = (Command.skip : Semantics.Program) then
                 Q localDb' cfg₂.globalDb
               else
                 LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                   ⟨body, [], startDb⟩
                   ⟨body', localDb', cfg₂.globalDb⟩)
        | .skip => I cfg₂.globalDb
        | _ => False := by
  classical
  intro cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro localDb snapshot currentDb currentBody hReachSnap hStart hReady hIcurrent hState
      cases hStart
      rcases hReady with hSkip | ⟨txnId', isolation', localDb', snapshot', hProgram, _⟩
      · cases hSkip
      · have hBodySkip : currentBody = (Command.skip : Semantics.Program) := by
          injection hProgram
        subst hBodySkip
        exact ⟨hIcurrent, by simpa using hState⟩
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro localDb snapshot currentDb currentBody hReachSnap hStart hReady hIcurrent hState
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txnRuntime_inv hActual with
            ⟨body', localDb', hNotSkip, hProgram, hDbEq, hLocal⟩ | hCommit
          · cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = currentDb := by
                  simpa using hDbEq
                subst dbMid
                have hLocalPath :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], startDb⟩
                        ⟨currentBody, localDb, currentDb⟩ := by
                    simpa [hNotSkip] using hState
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨body', localDb', currentDb⟩ := by
                  exact MultiStep.tail hLocalPath
                    (localInterleavedStep_of_localStep (relyMod R isolation.exec) txnId hLocal)
                -- After exec step, snapshot is updated to currentDb, and the new snapshot
                -- equals the new currentDb (which is still currentDb), so hReachSnap is refl.
                by_cases hNextSkip : body' = (Command.skip : Semantics.Program)
                · have hStartP : P [] startDb := by
                    exact (hPre [] startDb).2 ⟨rfl, hStartI⟩
                  subst body'
                  have hQ' : Q localDb' currentDb := by
                    exact hBody [] startDb
                      ⟨(Command.skip : Semantics.Program), localDb', currentDb⟩
                      hStartP
                      hLocalPath'
                      rfl
                  exact ih localDb' currentDb currentDb (Command.skip : Semantics.Program)
                    MultiStep.refl rfl hReady hIcurrent (by simpa using hQ')
                · exact ih localDb' currentDb currentDb body' MultiStep.refl rfl hReady hIcurrent
                    (by simpa [hNextSkip] using hLocalPath')
          · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq, _hCommitGuard⟩
            cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = Database.flush localDb currentDb := by
                  simpa using hDbEq
                subst hDbMid
                have hQ : Q localDb currentDb := by
                  simpa [hBodySkip] using hState
                have hCommitted : I (Database.flush localDb currentDb) := by
                  exact hPreserve _ _ hIcurrent (hGuarantee _ _ hQ)
                rcases skipGlobalFwd_preserves R I hStableI hRest hCommitted with ⟨hFinalSkip, hIFinal⟩
                simpa [hFinalSkip] using hIFinal
      | inr hRely =>
          cases cfgMid with
          | mk programMid dbMid =>
              rcases hRely with ⟨hProgram, hR⟩
              have hEqProgram :
                  programMid =
                    (.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program) := by
                simpa using hProgram
              subst hEqProgram
              have hIcurrent' : I dbMid := by
                exact hStableI _ _ hIcurrent hR
              have hReachSnap' : MultiStep R snapshot dbMid := MultiStep.tail hReachSnap hR
              by_cases hBodySkip : currentBody = (Command.skip : Semantics.Program)
              · have hQ : Q localDb currentDb := by
                  simpa [hBodySkip] using hState
                subst hBodySkip
                have hCommitMid : isolation.commit localDb snapshot dbMid := by
                  exact commitIsolation_of_future_ready hCommitStable hRest localDb snapshot dbMid
                    hReachSnap' rfl hReady
                have hCommitCurrent : isolation.commit localDb snapshot currentDb := by
                  exact (hCommitStable _ _ _ _ hReachSnap hCommitMid hR).1
                have hCommitRely :
                    relyMod R isolation.commit localDb currentDb dbMid := by
                  exact ⟨snapshot, hR, hCommitCurrent, hCommitMid⟩
                have hQ' : Q localDb dbMid := by
                  exact hQStable _ _ _ hQ hCommitRely
                exact ih localDb snapshot dbMid (Command.skip : Semantics.Program) hReachSnap' rfl
                  hReady hIcurrent' (by simpa using hQ')
              · have hLocalPath :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, currentDb⟩ := by
                  simpa [hBodySkip] using hState
                have hExecMid : isolation.exec localDb snapshot dbMid := by
                  exact execIsolation_of_future_ready hExecStable hRest
                    localDb snapshot dbMid currentBody hReachSnap' rfl hBodySkip hReady
                have hExecCurrent : isolation.exec localDb snapshot currentDb := by
                  exact (hExecStable _ _ _ _ hReachSnap hExecMid hR).1
                have hExecRely :
                    relyMod R isolation.exec localDb currentDb dbMid := by
                  exact ⟨snapshot, hR, hExecCurrent, hExecMid⟩
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, dbMid⟩ := by
                  exact MultiStep.tail hLocalPath (Or.inr ⟨rfl, rfl, hBodySkip, hExecRely⟩)
                exact ih localDb snapshot dbMid currentBody hReachSnap' rfl hReady hIcurrent'
                  (by simpa [hBodySkip] using hLocalPath')

theorem txnProgramFwd_sound {R : Rely} {txnId : TxnId}
    {I : Assertion} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee} :
    stableAssertion R I →
    stableIsolation R isolation.exec →
    stableIsolation R isolation.commit →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
    (∀ db db', I db → G db db' → I db') →
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ currentDb,
        cfg₁ = ⟨(.txn txnId isolation body : Semantics.Program), currentDb⟩ →
        ReadyToFinish cfg₂ →
        I currentDb →
        match cfg₂.program with
        | .txn _ _ _ => I cfg₂.globalDb
        | .txnRuntime _ _ localDb _ body' =>
            I cfg₂.globalDb ∧
              (body' = (Command.skip : Semantics.Program) → Q localDb cfg₂.globalDb)
        | .skip => I cfg₂.globalDb
        | _ => False := by
  intro hStableI hExecStable hCommitIsoStable hPre hBody hCommitStable hGuarantee hPreserve cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro currentDb hStart hReady hI
      cases hStart
      have : False := by
        simpa [ReadyToFinish] using hReady
      exact False.elim this
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro currentDb hStart hReady hI
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txn_inv hActual with ⟨hProgram, hDbEq⟩
          cases cfgMid with
          | mk programMid dbMid =>
              subst hProgram
              have hDbMid : dbMid = currentDb := by
                simpa using hDbEq
              subst dbMid
              by_cases hBodySkip : body = (Command.skip : Semantics.Program)
              · have hStartP : P [] currentDb := by
                  exact (hPre [] currentDb).2 ⟨rfl, hI⟩
                subst body
                have hQ : Q [] currentDb := by
                  exact hBody [] currentDb
                    ⟨(Command.skip : Semantics.Program), [], currentDb⟩
                    hStartP
                    MultiStep.refl
                    rfl
                have hRun :=
                  txnRuntimeFwd_sound hStableI hExecStable hPre hBody hCommitStable
                    hCommitIsoStable hGuarantee hPreserve hI
                    hRest [] currentDb currentDb (Command.skip : Semantics.Program)
                    MultiStep.refl rfl hReady hI
                    (by simpa using hQ)
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb snapshot body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hIvis, hState'⟩
                    refine ⟨hIvis, ?_⟩
                    intro hSkipFinal
                    simpa [hSkipFinal] using hState'
                | txn txnId' isolation' body' =>
                    simpa [hFinalProgram] using hRun
                | skip =>
                    simpa [hFinalProgram] using hRun
                | letE x expr body' =>
                    simpa [hFinalProgram] using hRun
                | ite cond thenBranch elseBranch =>
                    simpa [hFinalProgram] using hRun
                | seq left right =>
                    simpa [hFinalProgram] using hRun
                | insert expr =>
                    simpa [hFinalProgram] using hRun
                | delete source predicate =>
                    simpa [hFinalProgram] using hRun
                | select binder source predicate body' =>
                    simpa [hFinalProgram] using hRun
                | update source updateExpr predicate =>
                    simpa [hFinalProgram] using hRun
                | foreach source doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | foreachRuntime done remaining doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | par left right =>
                    simpa [hFinalProgram] using hRun
              · have hRun :=
                  txnRuntimeFwd_sound hStableI hExecStable hPre hBody hCommitStable
                    hCommitIsoStable hGuarantee hPreserve hI
                    hRest [] currentDb currentDb body MultiStep.refl rfl hReady hI
                    (by simpa [hBodySkip] using (MultiStep.refl :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], currentDb⟩
                        ⟨body, [], currentDb⟩))
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb snapshot body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hIvis, hState'⟩
                    refine ⟨hIvis, ?_⟩
                    intro hSkipFinal
                    simpa [hSkipFinal] using hState'
                | txn txnId' isolation' body' =>
                    simpa [hFinalProgram] using hRun
                | skip =>
                    simpa [hFinalProgram] using hRun
                | letE x expr body' =>
                    simpa [hFinalProgram] using hRun
                | ite cond thenBranch elseBranch =>
                    simpa [hFinalProgram] using hRun
                | seq left right =>
                    simpa [hFinalProgram] using hRun
                | insert expr =>
                    simpa [hFinalProgram] using hRun
                | delete source predicate =>
                    simpa [hFinalProgram] using hRun
                | select binder source predicate body' =>
                    simpa [hFinalProgram] using hRun
                | update source updateExpr predicate =>
                    simpa [hFinalProgram] using hRun
                | foreach source doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | foreachRuntime done remaining doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | par left right =>
                    simpa [hFinalProgram] using hRun
      | inr hRely =>
          cases cfgMid with
          | mk programMid dbMid =>
              rcases hRely with ⟨hProgram, hR⟩
              have hEqProgram : programMid = (.txn txnId isolation body : Semantics.Program) := by
                simpa using hProgram
              subst hEqProgram
              have hI' : I dbMid := by
                exact hStableI _ _ hI hR
              exact ih dbMid rfl hReady hI'

theorem txnRuntimeFwd_sound_post {R : Rely} {txnId : TxnId}
    {Ipre Ipost : Assertion} {isolation : IsolationSpec Database}
    {body : Semantics.Program} {P Q : BiAssertion}
    (hStableIpre : stableAssertion R Ipre)
    (hStableIpost : stableAssertion R Ipost)
    (hExecStable : stableIsolation R isolation.exec)
    (hPre : ∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ Ipre visibleDb)
    (hBody : LocalValid (relyMod R isolation.exec) txnId P body Q)
    (hQStable : stableBiAssertion (relyMod R isolation.commit) Q)
    (hCommitStable : stableIsolation R isolation.commit)
    (hCommitPost :
      ∀ localDb visibleDb,
        Ipre visibleDb → Q localDb visibleDb → Ipost (Database.flush localDb visibleDb))
    {startDb : Database} (hStartI : Ipre startDb) :
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ localDb snapshot currentDb currentBody,
        MultiStep R snapshot currentDb →
        cfg₁ =
          ⟨(.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program), currentDb⟩ →
        ReadyToFinish cfg₂ →
        Ipre currentDb →
        (if currentBody = (Command.skip : Semantics.Program) then
           Q localDb currentDb
         else
           LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
             ⟨body, [], startDb⟩
             ⟨currentBody, localDb, currentDb⟩) →
        match cfg₂.program with
        | .txnRuntime _ _ localDb' _ body' =>
            Ipre cfg₂.globalDb ∧
              (if body' = (Command.skip : Semantics.Program) then
                 Q localDb' cfg₂.globalDb
               else
                 LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                   ⟨body, [], startDb⟩
                   ⟨body', localDb', cfg₂.globalDb⟩)
        | .skip => Ipost cfg₂.globalDb
        | _ => False := by
  classical
  intro cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro localDb snapshot currentDb currentBody hReachSnap hStart hReady hIcurrent hState
      cases hStart
      rcases hReady with hSkip | ⟨txnId', isolation', localDb', snapshot', hProgram, _⟩
      · cases hSkip
      · have hBodySkip : currentBody = (Command.skip : Semantics.Program) := by
          injection hProgram
        subst hBodySkip
        exact ⟨hIcurrent, by simpa using hState⟩
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro localDb snapshot currentDb currentBody hReachSnap hStart hReady hIcurrent hState
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txnRuntime_inv hActual with
            ⟨body', localDb', hNotSkip, hProgram, hDbEq, hLocal⟩ | hCommit
          · cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = currentDb := by
                  simpa using hDbEq
                subst dbMid
                have hLocalPath :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], startDb⟩
                        ⟨currentBody, localDb, currentDb⟩ := by
                    simpa [hNotSkip] using hState
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨body', localDb', currentDb⟩ := by
                  exact MultiStep.tail hLocalPath
                    (localInterleavedStep_of_localStep (relyMod R isolation.exec) txnId hLocal)
                by_cases hNextSkip : body' = (Command.skip : Semantics.Program)
                · have hStartP : P [] startDb := by
                    exact (hPre [] startDb).2 ⟨rfl, hStartI⟩
                  subst body'
                  have hQ' : Q localDb' currentDb := by
                    exact hBody [] startDb
                      ⟨(Command.skip : Semantics.Program), localDb', currentDb⟩
                      hStartP
                      hLocalPath'
                      rfl
                  exact ih localDb' currentDb currentDb (Command.skip : Semantics.Program)
                    MultiStep.refl rfl hReady hIcurrent (by simpa using hQ')
                · exact ih localDb' currentDb currentDb body' MultiStep.refl rfl hReady hIcurrent
                    (by simpa [hNextSkip] using hLocalPath')
          · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq, _hCommitGuard⟩
            cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = Database.flush localDb currentDb := by
                  simpa using hDbEq
                subst hDbMid
                have hQ : Q localDb currentDb := by
                  simpa [hBodySkip] using hState
                have hCommitted : Ipost (Database.flush localDb currentDb) := by
                  exact hCommitPost _ _ hIcurrent hQ
                rcases skipGlobalFwd_preserves R Ipost hStableIpost hRest hCommitted with
                  ⟨hFinalSkip, hIFinal⟩
                simpa [hFinalSkip] using hIFinal
      | inr hRely =>
          cases cfgMid with
          | mk programMid dbMid =>
              rcases hRely with ⟨hProgram, hR⟩
              have hEqProgram :
                  programMid =
                    (.txnRuntime txnId isolation localDb snapshot currentBody : Semantics.Program) := by
                simpa using hProgram
              subst hEqProgram
              have hIcurrent' : Ipre dbMid := by
                exact hStableIpre _ _ hIcurrent hR
              have hReachSnap' : MultiStep R snapshot dbMid := MultiStep.tail hReachSnap hR
              by_cases hBodySkip : currentBody = (Command.skip : Semantics.Program)
              · have hQ : Q localDb currentDb := by
                  simpa [hBodySkip] using hState
                subst hBodySkip
                have hCommitMid : isolation.commit localDb snapshot dbMid := by
                  exact commitIsolation_of_future_ready hCommitStable hRest localDb snapshot dbMid
                    hReachSnap' rfl hReady
                have hCommitCurrent : isolation.commit localDb snapshot currentDb := by
                  exact (hCommitStable _ _ _ _ hReachSnap hCommitMid hR).1
                have hCommitRely :
                    relyMod R isolation.commit localDb currentDb dbMid := by
                  exact ⟨snapshot, hR, hCommitCurrent, hCommitMid⟩
                have hQ' : Q localDb dbMid := by
                  exact hQStable _ _ _ hQ hCommitRely
                exact ih localDb snapshot dbMid (Command.skip : Semantics.Program) hReachSnap' rfl
                  hReady hIcurrent' (by simpa using hQ')
              · have hLocalPath :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, currentDb⟩ := by
                  simpa [hBodySkip] using hState
                have hExecMid : isolation.exec localDb snapshot dbMid := by
                  exact execIsolation_of_future_ready hExecStable hRest
                    localDb snapshot dbMid currentBody hReachSnap' rfl hBodySkip hReady
                have hExecCurrent : isolation.exec localDb snapshot currentDb := by
                  exact (hExecStable _ _ _ _ hReachSnap hExecMid hR).1
                have hExecRely :
                    relyMod R isolation.exec localDb currentDb dbMid := by
                  exact ⟨snapshot, hR, hExecCurrent, hExecMid⟩
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, dbMid⟩ := by
                  exact MultiStep.tail hLocalPath (Or.inr ⟨rfl, rfl, hBodySkip, hExecRely⟩)
                exact ih localDb snapshot dbMid currentBody hReachSnap' rfl hReady hIcurrent'
                  (by simpa [hBodySkip] using hLocalPath')

theorem txnProgramFwd_sound_post {R : Rely} {txnId : TxnId}
    {Ipre Ipost : Assertion} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} :
    stableAssertion R Ipre →
    stableAssertion R Ipost →
    stableIsolation R isolation.exec →
    stableIsolation R isolation.commit →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ Ipre visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb,
      Ipre visibleDb → Q localDb visibleDb → Ipost (Database.flush localDb visibleDb)) →
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ currentDb,
        cfg₁ = ⟨(.txn txnId isolation body : Semantics.Program), currentDb⟩ →
        ReadyToFinish cfg₂ →
        Ipre currentDb →
        match cfg₂.program with
        | .txn _ _ _ => Ipre cfg₂.globalDb
        | .txnRuntime _ _ localDb _ body' =>
            Ipre cfg₂.globalDb ∧
              (body' = (Command.skip : Semantics.Program) → Q localDb cfg₂.globalDb)
        | .skip => Ipost cfg₂.globalDb
        | _ => False := by
  intro hStableIpre hStableIpost hExecStable hCommitIsoStable hPre hBody hCommitStable
    hCommitPost cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro currentDb hStart hReady hI
      cases hStart
      have : False := by
        simpa [ReadyToFinish] using hReady
      exact False.elim this
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro currentDb hStart hReady hI
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txn_inv hActual with ⟨hProgram, hDbEq⟩
          cases cfgMid with
          | mk programMid dbMid =>
              subst hProgram
              have hDbMid : dbMid = currentDb := by
                simpa using hDbEq
              subst dbMid
              by_cases hBodySkip : body = (Command.skip : Semantics.Program)
              · have hStartP : P [] currentDb := by
                  exact (hPre [] currentDb).2 ⟨rfl, hI⟩
                subst body
                have hQ : Q [] currentDb := by
                  exact hBody [] currentDb
                    ⟨(Command.skip : Semantics.Program), [], currentDb⟩
                    hStartP
                    MultiStep.refl
                    rfl
                have hRun :=
                  txnRuntimeFwd_sound_post hStableIpre hStableIpost hExecStable hPre hBody
                    hCommitStable hCommitIsoStable hCommitPost hI
                    hRest [] currentDb currentDb (Command.skip : Semantics.Program)
                    MultiStep.refl rfl hReady hI
                    (by simpa using hQ)
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb snapshot body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hIvis, hState'⟩
                    refine ⟨hIvis, ?_⟩
                    intro hSkipFinal
                    simpa [hSkipFinal] using hState'
                | txn txnId' isolation' body' =>
                    simpa [hFinalProgram] using hRun
                | skip =>
                    simpa [hFinalProgram] using hRun
                | letE x expr body' =>
                    simpa [hFinalProgram] using hRun
                | ite cond thenBranch elseBranch =>
                    simpa [hFinalProgram] using hRun
                | seq left right =>
                    simpa [hFinalProgram] using hRun
                | insert expr =>
                    simpa [hFinalProgram] using hRun
                | delete source predicate =>
                    simpa [hFinalProgram] using hRun
                | select binder source predicate body' =>
                    simpa [hFinalProgram] using hRun
                | update source updateExpr predicate =>
                    simpa [hFinalProgram] using hRun
                | foreach source doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | foreachRuntime done remaining doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | par left right =>
                    simpa [hFinalProgram] using hRun
              · have hRun :=
                  txnRuntimeFwd_sound_post hStableIpre hStableIpost hExecStable hPre hBody
                    hCommitStable hCommitIsoStable hCommitPost hI
                    hRest [] currentDb currentDb body MultiStep.refl rfl hReady hI
                    (by simpa [hBodySkip] using (MultiStep.refl :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], currentDb⟩
                        ⟨body, [], currentDb⟩))
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb snapshot body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hIvis, hState'⟩
                    refine ⟨hIvis, ?_⟩
                    intro hSkipFinal
                    simpa [hSkipFinal] using hState'
                | txn txnId' isolation' body' =>
                    simpa [hFinalProgram] using hRun
                | skip =>
                    simpa [hFinalProgram] using hRun
                | letE x expr body' =>
                    simpa [hFinalProgram] using hRun
                | ite cond thenBranch elseBranch =>
                    simpa [hFinalProgram] using hRun
                | seq left right =>
                    simpa [hFinalProgram] using hRun
                | insert expr =>
                    simpa [hFinalProgram] using hRun
                | delete source predicate =>
                    simpa [hFinalProgram] using hRun
                | select binder source predicate body' =>
                    simpa [hFinalProgram] using hRun
                | update source updateExpr predicate =>
                    simpa [hFinalProgram] using hRun
                | foreach source doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | foreachRuntime done remaining doneVar elemVar body' =>
                    simpa [hFinalProgram] using hRun
                | par left right =>
                    simpa [hFinalProgram] using hRun
      | inr hRely =>
          cases cfgMid with
          | mk programMid dbMid =>
              rcases hRely with ⟨hProgram, hR⟩
              have hEqProgram : programMid = (.txn txnId isolation body : Semantics.Program) := by
                simpa using hProgram
              subst hEqProgram
              have hI' : Ipre dbMid := by
                exact hStableIpre _ _ hI hR
              exact ih dbMid rfl hReady hI'

theorem txnGlobalValid_of_localValid_post {R : Rely} {Ipre Ipost : Assertion}
    {txnId : TxnId} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee} :
    stableAssertion R Ipre →
    stableAssertion R Ipost →
    stableIsolation R isolation.exec →
    stableIsolation R isolation.commit →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ Ipre visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
    (∀ localDb visibleDb,
      Ipre visibleDb → Q localDb visibleDb → Ipost (Database.flush localDb visibleDb)) →
    GlobalValid Ipre R (.txn txnId isolation body) G Ipost := by
  intro hStableIpre hStableIpost hExecStable hCommitIsoStable hPre hLocal hQstable
    hGuarantee hCommitPost
  intro db hI
  refine ⟨?_, ?_⟩
  · intro finalCfg hMulti hDone
    have hSingleFinal :
        SingleTxnProgram txnId finalCfg.program := by
      exact globalMultiStep_preserves_singleTxn hMulti SingleTxnProgram.txn
    have hSkip : finalCfg.program = (Command.skip : Semantics.Program) := by
      exact singleTxn_done_eq_skip hSingleFinal hDone
    have hReach :=
      txnProgramFwd_sound_post hStableIpre hStableIpost hExecStable hCommitIsoStable
        hPre hLocal hQstable hCommitPost (MultiStep.toFwd hMulti)
        db rfl (Or.inl hSkip) hI
    simpa [hSkip] using hReach
  · intro actualTxnId midCfg nextProgram nextDb hMulti hCommit
    have hSingleMid :
        SingleTxnProgram txnId midCfg.program := by
      exact globalMultiStep_preserves_singleTxn hMulti SingleTxnProgram.txn
    rcases txnCommitStep_of_singleTxn hSingleMid hCommit with ⟨rfl, hStep, hNextSkip⟩
    have hReadyMid : ReadyToFinish midCfg := by
      cases hMidProgram : midCfg.program with
      | txn txnId' isolation' body' =>
          have hStep' :
              Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep' with
          | txnStart =>
              cases hNextSkip
      | txnRuntime txnId' isolation' localDb snapshot currentBody =>
          have hStep' :
              Semantics.Step
                (.txnRuntime txnId' isolation' localDb snapshot currentBody)
                midCfg.globalDb
                nextProgram
                nextDb := by
            simpa [hMidProgram] using hStep
          rcases step_txnRuntime_inv hStep' with
            _hExec | hCommit
          · cases hNextSkip
            rcases _hExec with ⟨body', localDb', _hNotSkip, hProgram, _hDbEq, _hLocal⟩
            cases hProgram
          · rcases hCommit with ⟨hBodySkip, hProgram, _hDbEq, hCommitGuard⟩
            exact Or.inr ⟨txnId', isolation', localDb, snapshot,
              by simpa [hMidProgram, hBodySkip], hCommitGuard⟩
      | skip =>
          have hStep' :
              Semantics.Step (Command.skip : Semantics.Program) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          exact False.elim (no_step_from_program_skip hStep')
      | letE x expr body' =>
          have hStep' :
              Semantics.Step (.letE x expr body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | ite cond thenBranch elseBranch =>
          have hStep' :
              Semantics.Step (.ite cond thenBranch elseBranch) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | seq left right =>
          have hSeqSingle : SingleTxnProgram actualTxnId (.seq left right : Semantics.Program) := by
            simpa [hMidProgram] using hSingleMid
          cases hSeqSingle
      | insert expr =>
          have hStep' :
              Semantics.Step (.insert expr) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | delete source predicate =>
          have hStep' :
              Semantics.Step (.delete source predicate) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | select binder source predicate body' =>
          have hStep' :
              Semantics.Step (.select binder source predicate body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | update source updateExpr predicate =>
          have hStep' :
              Semantics.Step (.update source updateExpr predicate) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | foreach source doneVar elemVar body' =>
          have hStep' :
              Semantics.Step (.foreach source doneVar elemVar body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | foreachRuntime done remaining doneVar elemVar body' =>
          have hStep' :
              Semantics.Step
                (.foreachRuntime done remaining doneVar elemVar body')
                midCfg.globalDb
                nextProgram
                nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | par left right =>
          have hStep' :
              Semantics.Step (.par left right) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep' with
          | parLeft hLeft =>
              cases hNextSkip
          | parRight hRight =>
              cases hNextSkip
    have hReach :=
      txnProgramFwd_sound_post hStableIpre hStableIpost hExecStable hCommitIsoStable
        hPre hLocal hQstable hCommitPost (MultiStep.toFwd hMulti)
        db rfl hReadyMid hI
    cases hMidProgram : midCfg.program with
    | txn txnId' isolation' body' =>
        have hStep' :
            Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
          simpa [hMidProgram] using hStep
        cases hStep' with
        | txnStart =>
            cases hNextSkip
    | txnRuntime txnId' isolation' localDb snapshot currentBody =>
        rcases (by simpa [hMidProgram] using hReach) with ⟨_hIvisible, hState⟩
        have hStep' :
            Semantics.Step
              (.txnRuntime txnId' isolation' localDb snapshot currentBody)
              midCfg.globalDb
              nextProgram
              nextDb := by
          simpa [hMidProgram] using hStep
        rcases step_txnRuntime_inv hStep' with
          ⟨body', localDb', _hNotSkip, hProgram, hDbEq', _hLocal⟩ | hCommit
        · cases hNextSkip
          cases hProgram
        · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq', _hCommitGuard⟩
          have hQ := hState hBodySkip
          simpa [hDbEq'] using hGuarantee localDb midCfg.globalDb hQ
    | skip =>
        have hStep' :
            Semantics.Step (Command.skip : Semantics.Program) midCfg.globalDb nextProgram nextDb := by
          simpa [hMidProgram] using hStep
        exact False.elim (no_step_from_program_skip hStep')
    | letE x expr body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | ite cond thenBranch elseBranch =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | seq left right =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | insert expr =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | delete source predicate =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | select binder source predicate body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | update source updateExpr predicate =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | foreach source doneVar elemVar body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | foreachRuntime done remaining doneVar elemVar body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | par left right =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse

theorem txnGlobalValid_of_localValid {R : Rely} {I : Assertion} {txnId : TxnId}
    {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee} :
    stableAssertion R I →
    stableIsolation R isolation.exec →
    stableIsolation R isolation.commit →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
    (∀ db db', I db → G db db' → I db') →
    GlobalValid I R (.txn txnId isolation body) G I := by
  intro hStableI hExecStable hCommitIsoStable hPre hLocal hQstable hGuarantee hPreserve
  intro db hI
  refine ⟨?_, ?_⟩
  · intro finalCfg hMulti hDone
    have hSingleFinal :
        SingleTxnProgram txnId finalCfg.program := by
      exact globalMultiStep_preserves_singleTxn hMulti SingleTxnProgram.txn
    have hSkip : finalCfg.program = (Command.skip : Semantics.Program) := by
      exact singleTxn_done_eq_skip hSingleFinal hDone
    have hReach :=
      txnProgramFwd_sound hStableI hExecStable hCommitIsoStable hPre hLocal hQstable
        hGuarantee hPreserve (MultiStep.toFwd hMulti) db rfl (Or.inl hSkip) hI
    simpa [hSkip] using hReach
  · intro actualTxnId midCfg nextProgram nextDb hMulti hCommit
    have hSingleMid :
        SingleTxnProgram txnId midCfg.program := by
      exact globalMultiStep_preserves_singleTxn hMulti SingleTxnProgram.txn
    rcases txnCommitStep_of_singleTxn hSingleMid hCommit with ⟨rfl, hStep, hNextSkip⟩
    have hReadyMid : ReadyToFinish midCfg := by
      cases hMidProgram : midCfg.program with
      | txn txnId' isolation' body' =>
          have hStep' :
              Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep' with
          | txnStart =>
              cases hNextSkip
      | txnRuntime txnId' isolation' localDb snapshot currentBody =>
          have hStep' :
              Semantics.Step
                (.txnRuntime txnId' isolation' localDb snapshot currentBody)
                midCfg.globalDb
                nextProgram
                nextDb := by
            simpa [hMidProgram] using hStep
          rcases step_txnRuntime_inv hStep' with
            _hExec | hCommit
          · cases hNextSkip
            rcases _hExec with ⟨body', localDb', _hNotSkip, hProgram, _hDbEq, _hLocal⟩
            cases hProgram
          · rcases hCommit with ⟨hBodySkip, hProgram, _hDbEq, hCommitGuard⟩
            exact Or.inr ⟨txnId', isolation', localDb, snapshot,
              by simpa [hMidProgram, hBodySkip], hCommitGuard⟩
      | skip =>
          have hStep' :
              Semantics.Step (Command.skip : Semantics.Program) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          exact False.elim (no_step_from_program_skip hStep')
      | letE x expr body' =>
          have hStep' :
              Semantics.Step (.letE x expr body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | ite cond thenBranch elseBranch =>
          have hStep' :
              Semantics.Step (.ite cond thenBranch elseBranch) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | seq left right =>
          have hSeqSingle : SingleTxnProgram actualTxnId (.seq left right : Semantics.Program) := by
            simpa [hMidProgram] using hSingleMid
          cases hSeqSingle
      | insert expr =>
          have hStep' :
              Semantics.Step (.insert expr) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | delete source predicate =>
          have hStep' :
              Semantics.Step (.delete source predicate) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | select binder source predicate body' =>
          have hStep' :
              Semantics.Step (.select binder source predicate body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | update source updateExpr predicate =>
          have hStep' :
              Semantics.Step (.update source updateExpr predicate) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | foreach source doneVar elemVar body' =>
          have hStep' :
              Semantics.Step (.foreach source doneVar elemVar body') midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | foreachRuntime done remaining doneVar elemVar body' =>
          have hStep' :
              Semantics.Step
                (.foreachRuntime done remaining doneVar elemVar body')
                midCfg.globalDb
                nextProgram
                nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep'
      | par left right =>
          have hStep' :
              Semantics.Step (.par left right) midCfg.globalDb nextProgram nextDb := by
            simpa [hMidProgram] using hStep
          cases hStep' with
          | parLeft hLeft =>
              cases hNextSkip
          | parRight hRight =>
              cases hNextSkip
    have hReach :=
      txnProgramFwd_sound hStableI hExecStable hCommitIsoStable hPre hLocal hQstable
        hGuarantee hPreserve (MultiStep.toFwd hMulti) db rfl hReadyMid hI
    cases hMidProgram : midCfg.program with
    | txn txnId' isolation' body' =>
        have hStep' :
            Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
          simpa [hMidProgram] using hStep
        cases hStep' with
        | txnStart =>
            cases hNextSkip
    | txnRuntime txnId' isolation' localDb snapshot currentBody =>
        rcases (by simpa [hMidProgram] using hReach) with ⟨_hIvisible, hState⟩
        have hStep' :
            Semantics.Step
              (.txnRuntime txnId' isolation' localDb snapshot currentBody)
              midCfg.globalDb
              nextProgram
              nextDb := by
          simpa [hMidProgram] using hStep
        rcases step_txnRuntime_inv hStep' with
          ⟨body', localDb', _hNotSkip, hProgram, hDbEq', _hLocal⟩ | hCommit
        · cases hNextSkip
          cases hProgram
        · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq', _hCommitGuard⟩
          have hQ := hState hBodySkip
          simpa [hDbEq'] using hGuarantee localDb midCfg.globalDb hQ
    | skip =>
        have hStep' :
            Semantics.Step (Command.skip : Semantics.Program) midCfg.globalDb nextProgram nextDb := by
          simpa [hMidProgram] using hStep
        exact False.elim (no_step_from_program_skip hStep')
    | letE x expr body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | ite cond thenBranch elseBranch =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | seq left right =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | insert expr =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | delete source predicate =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | select binder source predicate body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | update source updateExpr predicate =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | foreach source doneVar elemVar body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | foreachRuntime done remaining doneVar elemVar body' =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse
    | par left right =>
        have hFalse : False := by
          simpa [hMidProgram] using hReach
        exact False.elim hFalse

theorem globalRG_sound {R : Rely} {I : Assertion} {program : Semantics.Program}
    {G : Guarantee} {Ipost : Assertion}
    (h : GlobalRG R I program G Ipost) :
    GlobalValid I R program G Ipost := by
  induction h with
  | txn hStableI hExecStable hCommitStable hPre hLocal hQstable hGuarantee hPreserve =>
      exact txnGlobalValid_of_localValid hStableI hExecStable hCommitStable hPre
        (localRG_sound hLocal) hQstable hGuarantee hPreserve
  | par hLeft hRight ihLeft ihRight =>
      exact globalValid_par ihLeft ihRight
  | conseq hRG ih hPre hStableI' hG hPreserve =>
      exact globalValid_conseq hPreserve ih hStableI'

theorem stableAssertion_false (P : Assertion) :
    stableAssertion (fun _ _ => False) P := by
  intro db db' hP hFalse
  exact False.elim hFalse

theorem stableBiAssertion_false (P : BiAssertion) :
    stableBiAssertion (fun _ _ _ => False) P := by
  intro localDb visibleDb visibleDb' hP hFalse
  exact False.elim hFalse

theorem stableIsolation_false (I : Database → Database → Database → Prop) :
    stableIsolation (fun _ _ => False) I := by
  intro localDb baseDb midDb finalDb _hReach hI hFalse
  exact False.elim hFalse

end Logic

end DbAppProgramLogic
