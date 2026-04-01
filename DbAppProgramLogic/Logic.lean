import DbAppProgramLogic.Semantics

namespace DbAppProgramLogic

abbrev Assertion := Database → Prop
abbrev BiAssertion := Database → Database → Prop
abbrev Rely := Database → Database → Prop
abbrev LocalRely := Database → Database → Database → Prop
abbrev Guarantee := Database → Database → Prop

structure LocalConfig (ι : Type) where
  cmd : Command ι Database
  localDb : Database
  visibleDb : Database

structure GlobalConfig where
  program : Semantics.Program
  globalDb : Database

namespace Logic

noncomputable local instance : DecidableEq Semantics.Program := by
  classical
  infer_instance

inductive MultiStep (step : α → α → Prop) : α → α → Prop where
  | refl {cfg} : MultiStep step cfg cfg
  | tail {cfg₁ cfg₂ cfg₃} : MultiStep step cfg₁ cfg₂ → step cfg₂ cfg₃ → MultiStep step cfg₁ cfg₃

inductive MultiStepFwd (step : α → α → Prop) : α → α → Prop where
  | refl {cfg} : MultiStepFwd step cfg cfg
  | cons {cfg₁ cfg₂ cfg₃} : step cfg₁ cfg₂ → MultiStepFwd step cfg₂ cfg₃ → MultiStepFwd step cfg₁ cfg₃

def stableAssertion (R : Rely) (P : Assertion) : Prop :=
  ∀ db db', P db → R db db' → P db'

def stableBiAssertion (R : LocalRely) (P : BiAssertion) : Prop :=
  ∀ localDb visibleDb visibleDb', P localDb visibleDb → R localDb visibleDb visibleDb' → P localDb visibleDb'

def stableIsolation (R : Rely) (I : Database → Database → Database → Prop) : Prop :=
  ∀ localDb baseDb midDb finalDb,
    I localDb baseDb finalDb →
    R midDb finalDb →
    I localDb baseDb midDb ∧ I localDb midDb finalDb

def relyMod (R : Rely) (I : Database → Database → Database → Prop) : LocalRely :=
  fun localDb visibleDb visibleDb' => R visibleDb visibleDb' ∧ I localDb visibleDb visibleDb'

def localInterleavedStep (R : LocalRely) (txnId : TxnId) :
    LocalConfig ι → LocalConfig ι → Prop
  | ⟨cmd, localDb, visibleDb⟩, ⟨cmd', localDb', visibleDb'⟩ =>
      (Semantics.LocalStep visibleDb txnId cmd localDb cmd' localDb' ∧ visibleDb' = visibleDb) ∨
        (cmd' = cmd ∧ localDb' = localDb ∧ cmd ≠ (Command.skip : Command ι Database) ∧
          R localDb visibleDb visibleDb')

def refreshVisible : Semantics.Program → Database → Semantics.Program
  | .txnRuntime txnId isolation localDb _ body, visibleDb =>
      .txnRuntime txnId isolation localDb visibleDb body
  | .par left right, visibleDb =>
      .par (refreshVisible left visibleDb) (refreshVisible right visibleDb)
  | program, _ =>
      program

def respectsRely (R : Rely) : Semantics.Program → Database → Database → Prop
  | .txnRuntime _ isolation localDb snapshot .skip, db, db' =>
      R db db' ∧ isolation.commit localDb snapshot db'
  | .txnRuntime _ isolation localDb snapshot _body, db, db' =>
      R db db' ∧ isolation.exec localDb snapshot db'
  | .par left right, db, db' =>
      respectsRely R left db db' ∧ respectsRely R right db db'
  | _, db, db' =>
      R db db'

def globalInterleavedStep (R : Rely) : GlobalConfig → GlobalConfig → Prop
  | ⟨program, globalDb⟩, ⟨program', globalDb'⟩ =>
      Semantics.Step program globalDb program' globalDb' ∨
        (program' = refreshVisible program globalDb' ∧ respectsRely R program globalDb globalDb')

abbrev LocalMultiStep (R : LocalRely) (txnId : TxnId) (ι : Type) :=
  MultiStep (localInterleavedStep (ι := ι) R txnId)

abbrev GlobalMultiStep (R : Rely) :=
  MultiStep (globalInterleavedStep R)

def LocalValid (R : LocalRely) (txnId : TxnId)
    (P : BiAssertion) (c : Command ι Database) (Q : BiAssertion) : Prop :=
  ∀ localDb visibleDb finalCfg,
    P localDb visibleDb →
    LocalMultiStep R txnId ι ⟨c, localDb, visibleDb⟩ finalCfg →
    finalCfg.cmd = (Command.skip : Command ι Database) →
    Q finalCfg.localDb finalCfg.visibleDb

def txnGuaranteed (R : Rely) (G : Guarantee) (program : Semantics.Program) (db : Database) : Prop :=
  ∀ midCfg nextProgram nextDb,
    GlobalMultiStep R ⟨program, db⟩ midCfg →
    Semantics.Step midCfg.program midCfg.globalDb nextProgram nextDb →
    nextProgram = (Command.skip : Semantics.Program) →
    G midCfg.globalDb nextDb

def GlobalValid (Ipre : Assertion) (R : Rely)
    (program : Semantics.Program) (G : Guarantee) (Ipost : Assertion) : Prop :=
  ∀ db,
    Ipre db →
      (∀ finalCfg,
        GlobalMultiStep R ⟨program, db⟩ finalCfg →
        finalCfg.program = (Command.skip : Semantics.Program) →
        Ipost finalCfg.globalDb) ∧
      txnGuaranteed R G program db

theorem txnGuaranteed_mono {R : Rely} {G G' : Guarantee}
    {program : Semantics.Program} {db : Database}
    (hTxn : txnGuaranteed R G program db)
    (hImp : ∀ db db', G db db' → G' db db') :
    txnGuaranteed R G' program db := by
  intro midCfg nextProgram nextDb hMulti hStep hSkip
  exact hImp _ _ (hTxn midCfg nextProgram nextDb hMulti hStep hSkip)

theorem globalValid_conseq {Ipre Imid Ipost : Assertion} {R : Rely}
    {program : Semantics.Program} {G G' : Guarantee}
    (hValid : GlobalValid Imid R program G Ipost)
    (hPre : ∀ db, Ipre db → Imid db)
    (hG : ∀ db db', G db db' → G' db db') :
    GlobalValid Ipre R program G' Ipost := by
  intro db hDb
  rcases hValid db (hPre _ hDb) with ⟨hPost, hTxn⟩
  refine ⟨hPost, txnGuaranteed_mono hTxn hG⟩

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
    {localDb visibleDb : Database} {currentBody program' : Semantics.Program} {db' : Database}
    (h :
      Semantics.Step (.txnRuntime txnId isolation localDb visibleDb currentBody) visibleDb program' db') :
    (∃ body' localDb',
        currentBody ≠ (Command.skip : Semantics.Program) ∧
        program' = (.txnRuntime txnId isolation localDb' visibleDb body' : Semantics.Program) ∧
        db' = visibleDb ∧
        Semantics.LocalStep visibleDb txnId currentBody localDb body' localDb') ∨
      (currentBody = (Command.skip : Semantics.Program) ∧
        program' = (Command.skip : Semantics.Program) ∧
        db' = Database.flush localDb visibleDb ∧
        isolation.commit localDb visibleDb visibleDb) := by
  cases h with
  | txnExec hExec hLocal =>
      left
      refine ⟨_, _, ?_, rfl, rfl, hLocal⟩
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
                    rcases hRely with ⟨hProgram, hRespect⟩
                    have hEqProgram : programMid = (Command.skip : Semantics.Program) := by
                      simpa [refreshVisible] using hProgram
                    have hI'' : I dbMid := by
                      exact hStable _ _ hI' (by simpa [respectsRely] using hRespect)
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

inductive GlobalRG (R : Rely) :
    Assertion → Semantics.Program → Guarantee → Assertion → Prop where
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

theorem txnRuntimeFwd_sound {R : Rely} {txnId : TxnId}
    {I : Assertion} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee}
    (hStableI : stableAssertion R I)
    (hPre : ∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb)
    (hBody : LocalValid (relyMod R isolation.exec) txnId P body Q)
    (hCommitStable : stableBiAssertion (relyMod R isolation.commit) Q)
    (hGuarantee : ∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb))
    (hPreserve : ∀ db db', I db → G db db' → I db')
    {startDb : Database} (hStartI : I startDb) :
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ localDb visibleDb currentBody,
        cfg₁ =
          ⟨(.txnRuntime txnId isolation localDb visibleDb currentBody : Semantics.Program), visibleDb⟩ →
        I visibleDb →
        (if currentBody = (Command.skip : Semantics.Program) then
           Q localDb visibleDb
         else
           LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
             ⟨body, [], startDb⟩
             ⟨currentBody, localDb, visibleDb⟩) →
        match cfg₂.program with
        | .txnRuntime _ _ localDb' visibleDb' body' =>
            cfg₂.globalDb = visibleDb' ∧
              I visibleDb' ∧
              (if body' = (Command.skip : Semantics.Program) then
                 Q localDb' visibleDb'
               else
                 LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                   ⟨body, [], startDb⟩
                   ⟨body', localDb', visibleDb'⟩)
        | .skip => I cfg₂.globalDb
        | _ => False := by
  classical
  intro cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro localDb visibleDb currentBody hStart hIvisible hState
      cases hStart
      exact ⟨rfl, hIvisible, hState⟩
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro localDb visibleDb currentBody hStart hIvisible hState
      cases hStart
      cases hStep with
      | inl hActual =>
          rcases step_txnRuntime_inv hActual with
            ⟨body', localDb', hNotSkip, hProgram, hDbEq, hLocal⟩ | hCommit
          · cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = visibleDb := by
                  simpa using hDbEq
                subst dbMid
                have hLocalPath :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], startDb⟩
                        ⟨currentBody, localDb, visibleDb⟩ := by
                    simpa [hNotSkip] using hState
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨body', localDb', visibleDb⟩ := by
                  exact MultiStep.tail hLocalPath
                    (localInterleavedStep_of_localStep (relyMod R isolation.exec) txnId hLocal)
                by_cases hNextSkip : body' = (Command.skip : Semantics.Program)
                · have hStartP : P [] startDb := by
                    exact (hPre [] startDb).2 ⟨rfl, hStartI⟩
                  subst body'
                  have hQ' : Q localDb' visibleDb := by
                    exact hBody [] startDb
                      ⟨(Command.skip : Semantics.Program), localDb', visibleDb⟩
                      hStartP
                      hLocalPath'
                      rfl
                  exact ih localDb' visibleDb (Command.skip : Semantics.Program) rfl hIvisible
                    (by simpa using hQ')
                · exact ih localDb' visibleDb body' rfl hIvisible
                    (by simpa [hNextSkip] using hLocalPath')
          · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq, hCommitGuard⟩
            cases cfgMid with
            | mk programMid dbMid =>
                subst hProgram
                have hDbMid : dbMid = Database.flush localDb visibleDb := by
                  simpa using hDbEq
                subst hDbMid
                have hQ : Q localDb visibleDb := by
                  simpa [hBodySkip] using hState
                have hCommitted : I (Database.flush localDb visibleDb) := by
                  exact hPreserve _ _ hIvisible (hGuarantee _ _ hQ)
                rcases skipGlobalFwd_preserves R I hStableI hRest hCommitted with ⟨hFinalSkip, hIFinal⟩
                simpa [hFinalSkip] using hIFinal
      | inr hRely =>
          cases cfgMid with
          | mk programMid dbMid =>
              rcases hRely with ⟨hProgram, hRespect⟩
              have hEqProgram :
                  programMid =
                    (.txnRuntime txnId isolation localDb dbMid currentBody : Semantics.Program) := by
                simpa [refreshVisible] using hProgram
              subst hEqProgram
              have hIvisible' : I dbMid := by
                by_cases hBodySkip : currentBody = (Command.skip : Semantics.Program)
                · have hRespect' : R visibleDb dbMid ∧ isolation.commit localDb visibleDb dbMid := by
                    simpa [respectsRely, hBodySkip] using hRespect
                  exact hStableI _ _ hIvisible hRespect'.1
                · have hRespect' : R visibleDb dbMid ∧ isolation.exec localDb visibleDb dbMid := by
                    simpa [respectsRely, hBodySkip] using hRespect
                  exact hStableI _ _ hIvisible hRespect'.1
              by_cases hBodySkip : currentBody = (Command.skip : Semantics.Program)
              · have hQ : Q localDb visibleDb := by
                  simpa [hBodySkip] using hState
                have hCommitRely :
                    relyMod R isolation.commit localDb visibleDb dbMid := by
                  simpa [relyMod, respectsRely, hBodySkip] using hRespect
                have hQ' : Q localDb dbMid := by
                  exact hCommitStable _ _ _ hQ hCommitRely
                exact ih localDb dbMid currentBody rfl hIvisible'
                  (by simpa [hBodySkip] using hQ')
              · have hLocalPath :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, visibleDb⟩ := by
                  simpa [hBodySkip] using hState
                have hExecRely :
                    relyMod R isolation.exec localDb visibleDb dbMid := by
                  simpa [relyMod, respectsRely, hBodySkip] using hRespect
                have hLocalPath' :
                    LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                      ⟨body, [], startDb⟩
                      ⟨currentBody, localDb, dbMid⟩ := by
                  exact MultiStep.tail hLocalPath (Or.inr ⟨rfl, rfl, hBodySkip, hExecRely⟩)
                exact ih localDb dbMid currentBody rfl hIvisible'
                  (by simpa [hBodySkip] using hLocalPath')

theorem txnProgramFwd_sound {R : Rely} {txnId : TxnId}
    {I : Assertion} {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee} :
    stableAssertion R I →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
    (∀ db db', I db → G db db' → I db') →
    ∀ {cfg₁ cfg₂ : GlobalConfig},
      MultiStepFwd (globalInterleavedStep R) cfg₁ cfg₂ →
      ∀ currentDb,
        cfg₁ = ⟨(.txn txnId isolation body : Semantics.Program), currentDb⟩ →
        I currentDb →
        match cfg₂.program with
        | .txn _ _ _ => I cfg₂.globalDb
        | .txnRuntime _ _ localDb visibleDb body' =>
            cfg₂.globalDb = visibleDb ∧
              I visibleDb ∧
              (body' = (Command.skip : Semantics.Program) → Q localDb visibleDb)
        | .skip => I cfg₂.globalDb
        | _ => False := by
  intro hStableI hPre hBody hCommitStable hGuarantee hPreserve cfg₁ cfg₂ hPath
  induction hPath with
  | refl =>
      intro currentDb hStart hI
      cases hStart
      simpa using hI
  | @cons cfgStart cfgMid cfgFinal hStep hRest ih =>
      intro currentDb hStart hI
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
                  txnRuntimeFwd_sound hStableI hPre hBody hCommitStable hGuarantee hPreserve hI
                    hRest [] currentDb (Command.skip : Semantics.Program) rfl hI (by simpa using hQ)
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb visibleDb body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hDbEq', hIvis, hState'⟩
                    refine ⟨hDbEq', hIvis, ?_⟩
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
                  txnRuntimeFwd_sound hStableI hPre hBody hCommitStable hGuarantee hPreserve hI
                    hRest [] currentDb body rfl hI
                    (by simpa [hBodySkip] using (MultiStep.refl :
                      LocalMultiStep (relyMod R isolation.exec) txnId (IsolationSpec Database)
                        ⟨body, [], currentDb⟩
                        ⟨body, [], currentDb⟩))
                cases hFinalProgram : cfgFinal.program with
                | txnRuntime txnId' isolation' localDb visibleDb body' =>
                    rcases (by simpa [hFinalProgram] using hRun) with ⟨hDbEq', hIvis, hState'⟩
                    refine ⟨hDbEq', hIvis, ?_⟩
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
              rcases hRely with ⟨hProgram, hRespect⟩
              have hEqProgram : programMid = (.txn txnId isolation body : Semantics.Program) := by
                simpa [refreshVisible] using hProgram
              subst hEqProgram
              have hR : R currentDb dbMid := by
                simpa [respectsRely] using hRespect
              have hI' : I dbMid := by
                exact hStableI _ _ hI hR
              exact ih dbMid rfl hI'

theorem txnGlobalValid_of_localValid {R : Rely} {I : Assertion} {txnId : TxnId}
    {isolation : IsolationSpec Database} {body : Semantics.Program}
    {P Q : BiAssertion} {G : Guarantee} :
    stableAssertion R I →
    (∀ localDb visibleDb, P localDb visibleDb ↔ localDb = [] ∧ I visibleDb) →
    LocalValid (relyMod R isolation.exec) txnId P body Q →
    stableBiAssertion (relyMod R isolation.commit) Q →
    (∀ localDb visibleDb, Q localDb visibleDb → G visibleDb (Database.flush localDb visibleDb)) →
    (∀ db db', I db → G db db' → I db') →
    GlobalValid I R (.txn txnId isolation body) G I := by
  intro hStableI hPre hLocal hQstable hGuarantee hPreserve
  intro db hI
  refine ⟨?_, ?_⟩
  · intro finalCfg hMulti hSkip
    have hReach :=
      txnProgramFwd_sound hStableI hPre hLocal hQstable hGuarantee hPreserve
        (MultiStep.toFwd hMulti) db rfl hI
    simpa [hSkip] using hReach
  · intro midCfg nextProgram nextDb hMulti hStep hNextSkip
    have hReach :=
      txnProgramFwd_sound hStableI hPre hLocal hQstable hGuarantee hPreserve
        (MultiStep.toFwd hMulti) db rfl hI
    cases hMidProgram : midCfg.program with
    | txn txnId' isolation' body' =>
        have hStep' :
            Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
          simpa [hMidProgram] using hStep
        cases hStep' with
        | txnStart =>
            cases hNextSkip
    | txnRuntime txnId' isolation' localDb visibleDb currentBody =>
        rcases (by simpa [hMidProgram] using hReach) with ⟨hDbEq, _hIvisible, hState⟩
        have hStep' :
            Semantics.Step
              (.txnRuntime txnId' isolation' localDb visibleDb currentBody)
              visibleDb
              nextProgram
              nextDb := by
          simpa [hMidProgram, hDbEq] using hStep
        rcases step_txnRuntime_inv hStep' with
          ⟨body', localDb', _hNotSkip, hProgram, hDbEq', _hLocal⟩ | hCommit
        · cases hNextSkip
          cases hProgram
        · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq', _hCommitGuard⟩
          have hQ := hState hBodySkip
          simpa [hDbEq, hDbEq'] using hGuarantee localDb visibleDb hQ
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
      intro db hI
      refine ⟨?_, ?_⟩
      · intro finalCfg hMulti hSkip
        have hReach :=
          txnProgramFwd_sound hStableI hPre (localRG_sound hLocal) hQstable hGuarantee hPreserve
            (MultiStep.toFwd hMulti) db rfl hI
        simpa [hSkip] using hReach
      · intro midCfg nextProgram nextDb hMulti hStep hNextSkip
        have hReach :=
          txnProgramFwd_sound hStableI hPre (localRG_sound hLocal) hQstable hGuarantee hPreserve
            (MultiStep.toFwd hMulti) db rfl hI
        cases hMidProgram : midCfg.program with
        | txn txnId' isolation' body' =>
            have hStep' :
                Semantics.Step (.txn txnId' isolation' body') midCfg.globalDb nextProgram nextDb := by
              simpa [hMidProgram] using hStep
            cases hStep' with
            | txnStart =>
                cases hNextSkip
        | txnRuntime txnId' isolation' localDb visibleDb currentBody =>
            rcases (by simpa [hMidProgram] using hReach) with ⟨hDbEq, _hIvisible, hState⟩
            have hStep' :
                Semantics.Step
                  (.txnRuntime txnId' isolation' localDb visibleDb currentBody)
                  visibleDb
                  nextProgram
                  nextDb := by
              simpa [hMidProgram, hDbEq] using hStep
            rcases step_txnRuntime_inv hStep' with
              ⟨body', localDb', _hNotSkip, hProgram, hDbEq', _hLocal⟩ | hCommit
            · cases hNextSkip
              cases hProgram
            · rcases hCommit with ⟨hBodySkip, hProgram, hDbEq', _hCommitGuard⟩
              have hQ := hState hBodySkip
              simpa [hDbEq, hDbEq'] using hGuarantee localDb visibleDb hQ
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
  intro localDb baseDb midDb finalDb hI hFalse
  exact False.elim hFalse

end Logic

end DbAppProgramLogic
