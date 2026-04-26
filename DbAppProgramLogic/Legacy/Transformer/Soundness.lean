import DbAppProgramLogic.Legacy.Transformer.SetEffect
import DbAppProgramLogic.Legacy.Transformer.PaperEffect

namespace DbAppProgramLogic

namespace Transformer

theorem inferenceSoundEnv_all (txnId : TxnId) :
    ∀ env body, inferenceSoundEnv txnId env body (inferEffect txnId env body)
  | env, .skip =>
      inferenceSoundEnv_skip txnId env
  | env, .letE x expr body =>
      inferenceSoundEnv_let txnId env x expr body
        (fun value _ => inferenceSoundEnv_all txnId (env.insert x value) body)
  | env, .ite cond thenBranch elseBranch =>
      inferenceSoundEnv_ite txnId env cond thenBranch elseBranch
        (inferenceSoundEnv_all txnId env thenBranch)
        (inferenceSoundEnv_all txnId env elseBranch)
  | env, .seq left right =>
      inferenceSoundEnv_seq txnId env left right
        (inferenceSoundEnv_all txnId env left)
        (inferenceSoundEnv_all txnId env right)
  | env, .insert expr =>
      inferenceSoundEnv_insert txnId env expr
  | env, .delete source predicate =>
      inferenceSoundEnv_delete txnId env source predicate
  | env, .select binder source predicate body =>
      inferenceSoundEnv_select txnId env binder source predicate body
        (fun selected => inferenceSoundEnv_all txnId (env.insert binder (.set selected)) body)
  | env, .update source updateExpr predicate =>
      inferenceSoundEnv_update txnId env source updateExpr predicate
  | env, .foreach source doneVar elemVar body =>
      inferenceSoundEnv_foreach txnId env source doneVar elemVar body
        (fun done current => inferenceSoundEnv_all txnId (foreachEnv env doneVar elemVar done current) body)
  | env, .foreachRuntime done remaining doneVar elemVar body =>
      inferenceSoundEnv_foreachRuntime txnId env done remaining doneVar elemVar body
        (fun done current => inferenceSoundEnv_all txnId (foreachEnv env doneVar elemVar done current) body)
  | env, .txn innerTxnId isolation body => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer
  | env, .txnRuntime innerTxnId isolation localDb snapshot body => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer
  | env, .par left right => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer

theorem inferenceSound_all (txnId : TxnId) (body : Semantics.Program) :
    inferenceSound txnId body (inferEffect txnId [] body) := by
  exact inferenceSound_of_env_empty txnId body (inferEffect txnId [] body)
    (inferenceSoundEnv_all txnId [] body)

theorem vcg_effect_sound (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program) :
    inferenceSound txnId body (vcg R I G txnId isolation body).effect := by
  simpa [vcg] using inferenceSound_all txnId body

theorem vcgForTxn_sound (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program) :
    ∃ info,
      vcgForTxn R I G (.txn txnId isolation body) = some info ∧
      inferenceSound txnId body info.effect := by
  refine ⟨vcg R I G txnId isolation body, rfl, ?_⟩
  exact vcg_effect_sound R I G txnId isolation body

theorem vcg_setSound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : (vcg R I G txnId isolation body).effect visibleDb = some localDb) :
    denotesRows (SetLanguage.Env.ofDatabases [] visibleDb) s localDb := by
  intro row
  exact inferSetEffect_sound txnId [] body visibleDb s localDb row hSet
    (by simpa [vcg] using hEffect)

theorem vcgForTxn_setSound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : TransactionVCG) (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInfo : vcgForTxn R I G (.txn txnId isolation body) = some info)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : info.effect visibleDb = some localDb) :
    denotesRows (SetLanguage.Env.ofDatabases [] visibleDb) s localDb := by
  simp [vcgForTxn] at hInfo
  subst info
  exact vcg_setSound txnId isolation body visibleDb localDb s hSet hEffect

theorem vcg_setWeaken_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (absVar : VarName) (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : (vcg R I G txnId isolation body).effect visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  exact inferSetEffect_weaken_sound I absVar txnId [] body visibleDb s localDb row hInv hSet
    (by simpa [vcg] using hEffect) hRow

theorem vcgForTxn_setWeaken_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (absVar : VarName) (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : TransactionVCG) (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInfo : vcgForTxn R I G (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : info.effect visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  simp [vcgForTxn] at hInfo
  subst info
  exact vcg_setWeaken_sound absVar txnId isolation body visibleDb localDb s row hInv hSet hEffect hRow

/-- The weakened symbolic postcondition used at the transaction interface. This packages the exact
symbolic effect together with existential abstraction over the current global database. -/
def symbolicVcg (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program) : SetEffect :=
  weakenSetEffect I absVar (inferSetEffect txnId [] body)

def symbolicVcgForTxn (I : Assertion) (absVar : VarName) : Semantics.Program → Option SetEffect
  | .txn txnId _isolation body => some (symbolicVcg I absVar txnId body)
  | _ => none

/-- Convenience wrapper for evaluating `symbolicVcgForTxn` on a concrete visible database. -/
def symbolicPostForTxn (I : Assertion) (absVar : VarName)
    (program : Semantics.Program) (visibleDb : Database) : Option SetLanguage.SetExpr := do
  let info ← symbolicVcgForTxn I absVar program
  info visibleDb

theorem symbolicVcg_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) row := by
  have hSym :
      symbolicVcg I absVar txnId body visibleDb =
        some (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) := by
    simp [symbolicVcg, weakenSetEffect, hSet]
  rw [hSym]
  simp
  exact inferSetEffect_weaken_sound I absVar txnId [] body visibleDb s localDb row hInv hSet hEffect hRow

theorem symbolicVcg_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (row : Row)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) row := by
  rcases inferSetEffect_some_of_inferEffect_some txnId [] body visibleDb localDb hInferable hEffect with
    ⟨s, hSet⟩
  exact symbolicVcg_sound I absVar txnId body visibleDb localDb s row hInv hSet hEffect hRow

theorem symbolicVcg_some_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    ∃ s, symbolicVcg I absVar txnId body visibleDb = some s := by
  rcases inferSetEffect_some_of_inferEffect_some txnId [] body visibleDb localDb hInferable hEffect with
    ⟨s, hSet⟩
  refine ⟨SetLanguage.weakenToInvariant absVar (assertionFormula I) s, ?_⟩
  simp [symbolicVcg, weakenSetEffect, hSet]

theorem symbolicVcg_eq_some_get!_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    symbolicVcg I absVar txnId body visibleDb =
      some (Option.get! (symbolicVcg I absVar txnId body visibleDb)) := by
  rcases symbolicVcg_some_of_inferEffect_some I absVar txnId body visibleDb localDb hInferable hEffect with
    ⟨s, hSome⟩
  apply option_eq_some_get!
  intro hNone
  rw [hNone] at hSome
  cases hSome

theorem symbolicVcg_overapprox_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) localDb := by
  exact inferSetEffect_weaken_overapprox I absVar txnId [] body visibleDb s localDb hInv hSet hEffect

theorem symbolicVcg_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) localDb := by
  intro row hRow
  exact symbolicVcg_sound_of_inferEffect_some I absVar txnId body visibleDb localDb row
    hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) row := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_sound I absVar txnId body visibleDb localDb s row hInv hSet hEffect hRow

theorem symbolicVcgForTxn_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (row : Row)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) row := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_sound_of_inferEffect_some I absVar txnId body visibleDb localDb row
    hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_some_at_visibleDb_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    ∃ s, info visibleDb = some s := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_some_of_inferEffect_some I absVar txnId body visibleDb localDb hInferable hEffect

theorem symbolicVcgForTxn_eq_some_get!_at_visibleDb_of_inferEffect_some
    (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    info visibleDb = some (Option.get! (info visibleDb)) := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_eq_some_get!_of_inferEffect_some I absVar txnId body visibleDb localDb
    hInferable hEffect

theorem symbolicPostForTxn_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (row : Row)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb)) row := by
  have hInfo :
      symbolicVcgForTxn I absVar (.txn txnId isolation body) =
        some (symbolicVcg I absVar txnId body) := by
    simp [symbolicVcgForTxn]
  have hShape :
      symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb =
        symbolicVcg I absVar txnId body visibleDb := by
    simp [symbolicPostForTxn, symbolicVcgForTxn]
  rw [hShape]
  exact symbolicVcgForTxn_sound_of_inferEffect_some I absVar txnId isolation body
    (symbolicVcg I absVar txnId body) visibleDb localDb row hInfo hInferable hInv hEffect hRow

theorem symbolicPostForTxn_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb))
      localDb := by
  intro row hRow
  exact symbolicPostForTxn_sound_of_inferEffect_some I absVar txnId isolation body
    visibleDb localDb row hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_overapprox_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) localDb := by
  have hInfo' := hInfo
  simp [symbolicVcgForTxn] at hInfo'
  subst info
  exact symbolicVcg_overapprox_sound I absVar txnId body visibleDb localDb s hInv hSet hEffect

theorem symbolicVcgForTxn_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) localDb := by
  intro row hRow
  exact symbolicVcgForTxn_sound_of_inferEffect_some I absVar txnId isolation body info
    visibleDb localDb row hInfo hInferable hInv hEffect hRow

theorem effectStable_false (F : TxnEffect) :
    effectStable (fun _ _ _ => False) F := by
  intro localDb visibleDb visibleDb' hFalse
  exact False.elim hFalse

theorem effectPost_stable_of_commitStable {R : Rely} {I : Assertion}
    {isolation : IsolationSpec Database} {F : TxnEffect}
    (hEffect : effectStable (Logic.relyMod R isolation.commit) F)
    (hI : Logic.stableAssertion R I) :
    Logic.stableBiAssertion (Logic.relyMod R isolation.commit) (effectPost I F) := by
  intro localDb visibleDb visibleDb' hPost hRely
  rcases hPost with ⟨hEffectDb, hIvisible⟩
  rcases hRely with ⟨baseDb, hR, hIsoVisible, hIsoVisible'⟩
  constructor
  · have hEq : F visibleDb = F visibleDb' := by
      exact hEffect localDb visibleDb visibleDb' ⟨baseDb, hR, hIsoVisible, hIsoVisible'⟩
    rw [hEq] at hEffectDb
    exact hEffectDb
  · exact hI _ _ hIvisible hR

theorem effectPost_guarantee {G : Guarantee} {I : Assertion} {F : TxnEffect}
    (hGuarantee : guaranteeValid G F) :
    ∀ localDb visibleDb, effectPost I F localDb visibleDb → G visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hPost
  exact hGuarantee visibleDb localDb hPost.1

theorem effectLocalValid_false (txnId : TxnId) (body : Semantics.Program)
    (I : Assertion) (F : TxnEffect)
    (hDefined : effectDefinedOn I F)
    (hSound : inferenceSound txnId body F) :
    Logic.LocalValid (fun _ _ _ => False) txnId
      (fun localDb visible => localDb = [] ∧ I visible)
      body
      (effectPost I F) := by
  intro localDb visibleDb finalCfg hPre hMulti hSkip
  rcases hPre with ⟨hLocalEq, hIvisible⟩
  subst hLocalEq
  rcases hDefined visibleDb hIvisible with ⟨deltaDb, hDelta⟩
  have hPost :=
    hSound visibleDb deltaDb hDelta
      [] visibleDb finalCfg
      (by simp)
      hMulti
      hSkip
  rcases hPost with ⟨hLocalFinal, hVisibleFinal⟩
  constructor
  · simpa [effectPost, hLocalFinal, hVisibleFinal] using hDelta
  · simpa [hVisibleFinal] using hIvisible

/--
Lift the concrete/no-interference inference theorem to any rely that leaves the visible database
unchanged. This is the useful case for identity-style relies and snapshot-style execution relies.
-/
theorem effectLocalValid_of_stutterRely (txnId : TxnId) (body : Semantics.Program)
    (I : Assertion) (F : TxnEffect) (R : LocalRely)
    (hDefined : effectDefinedOn I F)
    (hSound : inferenceSound txnId body F)
    (hSilent : ∀ localDb visibleDb visibleDb', R localDb visibleDb visibleDb' → visibleDb' = visibleDb) :
    Logic.LocalValid R txnId
      (fun localDb visible => localDb = [] ∧ I visible)
      body
      (effectPost I F) := by
  exact Logic.localValid_of_stutterRely
    (effectLocalValid_false txnId body I F hDefined hSound)
    hSilent

theorem vcg_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hStableI : Logic.stableAssertion R I)
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hLocal :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I (vcg R I G txnId isolation body).effect))
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
    (hCommit : (vcg R I G txnId isolation body).commitStable)
    (hGuarantee : (vcg R I G txnId isolation body).guaranteeOk)
    (hPreserve : (vcg R I G txnId isolation body).preservesInvariant) :
    Logic.GlobalValid I R (.txn txnId isolation body) G I := by
  have hCommit' :
      effectStable (Logic.relyMod R isolation.commit) (vcg R I G txnId isolation body).effect := by
    simpa [vcg] using hCommit
  have hGuarantee' :
      guaranteeValid G (vcg R I G txnId isolation body).effect := by
    simpa [vcg] using hGuarantee
  have hPreserve' : ∀ db db', I db → G db db' → I db' := by
    simpa [vcg] using hPreserve
  refine Logic.txnGlobalValid_of_localValid hStableI hExecStable hCommitIsoStable ?_ hLocal ?_ ?_ hPreserve'
  · intro localDb visibleDb
    constructor <;> intro h <;> simpa using h
  · exact effectPost_stable_of_commitStable hCommit' hStableI
  · exact effectPost_guarantee hGuarantee'

/--
Practical variant of `vcg_sound` for execution relies that are observationally silent: the visible
database may take rely steps, but every such step preserves the currently observed snapshot.

This is the strongest theorem currently derivable from the concrete `inferEffect` pipeline without
moving to the paper's fully symbolic conditional rule.
-/
theorem vcg_sound_stutter {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hStableI : Logic.stableAssertion R I)
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hExecSilent :
      ∀ localDb visibleDb visibleDb',
        Logic.relyMod R isolation.exec localDb visibleDb visibleDb' →
        visibleDb' = visibleDb)
    (hDefined : effectDefinedOn I ((vcg R I G txnId isolation body).effect))
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
    (hCommit : (vcg R I G txnId isolation body).commitStable)
    (hGuarantee : (vcg R I G txnId isolation body).guaranteeOk)
    (hPreserve : (vcg R I G txnId isolation body).preservesInvariant) :
    Logic.GlobalValid I R (.txn txnId isolation body) G I := by
  have hLocal :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I ((vcg R I G txnId isolation body).effect)) := by
    exact effectLocalValid_of_stutterRely txnId body I _
      (Logic.relyMod R isolation.exec)
      hDefined
      (vcg_effect_sound R I G txnId isolation body)
      hExecSilent
  exact vcg_sound txnId isolation body
    hStableI
    hExecStable
    hLocal
    hCommitIsoStable
    hCommit
    hGuarantee
    hPreserve

theorem vcg_sound_false {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      effectDefinedOn I ((vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee : (vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve : (vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Logic.GlobalValid I (fun _ _ => False) (.txn txnId isolation body) G I := by
  have hLocal :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I ((vcg (fun _ _ => False) I G txnId isolation body).effect)) := by
    exact effectLocalValid_false txnId body I _ hDefined
      (vcg_effect_sound (fun _ _ => False) I G txnId isolation body)
  have hLocal' :
      Logic.LocalValid (Logic.relyMod (fun _ _ => False) isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I ((vcg (fun _ _ => False) I G txnId isolation body).effect)) := by
    intro localDb visibleDb finalCfg hPre hMulti hSkip
    have stripFalse :
        ∀ {cfg₁ cfg₂ : LocalConfig (IsolationSpec Database)},
          Logic.LocalMultiStep (Logic.relyMod (fun _ _ => False) isolation.exec)
              txnId (IsolationSpec Database) cfg₁ cfg₂ →
          Logic.LocalMultiStep (fun _ _ _ => False)
              txnId (IsolationSpec Database) cfg₁ cfg₂ := by
      intro cfg₁ cfg₂ hPath
      induction hPath with
      | refl =>
          exact Logic.MultiStep.refl
      | tail hPrev hLast ih =>
          refine Logic.MultiStep.tail ih ?_
          cases hLast with
          | inl hLocalStep =>
              exact Or.inl hLocalStep
          | inr hRely =>
              rcases hRely with ⟨_, _, _, hRely⟩
              rcases hRely with ⟨_, hFalse, _, _⟩
              exact False.elim hFalse
    have hMulti' :
        Logic.LocalMultiStep (fun _ _ _ => False) txnId (IsolationSpec Database)
          ⟨body, localDb, visibleDb⟩ finalCfg := by
      exact stripFalse hMulti
    exact hLocal localDb visibleDb finalCfg hPre
      hMulti'
      hSkip
  have hCommit : (vcg (fun _ _ => False) I G txnId isolation body).commitStable := by
    simp [vcg, Logic.relyMod, effectStable]
  exact vcg_sound txnId isolation body
    (Logic.stableAssertion_false I)
    (Logic.stableIsolation_false isolation.exec)
    hLocal'
    (Logic.stableIsolation_false isolation.commit)
    hCommit
    hGuarantee
    hPreserve


end Transformer

end DbAppProgramLogic
