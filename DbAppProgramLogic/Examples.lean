import DbAppProgramLogic.FirstOrder

namespace DbAppProgramLogic

namespace Examples

def nonnegativeBalances : Assertion :=
  fun db =>
    ∀ row, row ∈ db →
      match row.visible.lookup? "bal" with
      | some (.int bal) => 0 <= bal
      | _ => True

def zeroBalanceRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 0)]⟩

def zeroBalanceRow : Row :=
  Row.fromInsert 0 zeroBalanceRecord

def zeroBalanceInsertBody : Semantics.Program :=
  .insert (.record [("id", Expr.int 1), ("bal", Expr.int 0)])

def zeroBalanceGuarantee : Guarantee :=
  fun db db' => db' = Database.flush [zeroBalanceRow] db

theorem nonnegativeBalances_flush_zeroBalanceRow {db : Database}
    (hDb : nonnegativeBalances db) :
    nonnegativeBalances (Database.flush [zeroBalanceRow] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [zeroBalanceRow, zeroBalanceRecord, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [zeroBalanceRow, zeroBalanceRecord, Row.fromInsert, RecordLit.lookup?]

theorem zeroBalance_insert_eval :
    Expr.eval (.record [("id", Expr.int 1), ("bal", Expr.int 0)]) =
      some (.record zeroBalanceRecord) := by
  native_decide

theorem zeroBalance_effect (visibleDb : Database) :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances zeroBalanceGuarantee
      0 Database.uniqueIds zeroBalanceInsertBody).effect visibleDb = some [zeroBalanceRow] := by
  simp [Transformer.vcg, Transformer.inferEffect, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, zeroBalanceInsertBody]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_setEffect (visibleDb : Database) :
    Transformer.inferSetEffect 0 [] zeroBalanceInsertBody visibleDb =
      some (SetLanguage.singleton zeroBalanceRow) := by
  simp [Transformer.inferSetEffect, Transformer.insertSetExpr, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, zeroBalanceInsertBody]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_effect_defined :
    Transformer.effectDefinedOn nonnegativeBalances
      ((Transformer.vcg (fun _ _ => False) nonnegativeBalances zeroBalanceGuarantee
        0 Database.uniqueIds zeroBalanceInsertBody).effect) := by
  intro visibleDb _hInv
  exact ⟨[zeroBalanceRow], zeroBalance_effect visibleDb⟩

theorem zeroBalance_guarantee_ok :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances zeroBalanceGuarantee
      0 Database.uniqueIds zeroBalanceInsertBody).guaranteeOk := by
  intro visibleDb localDb hEffect
  have hConst :
      Transformer.inferEffect 0 [] zeroBalanceInsertBody visibleDb = some [zeroBalanceRow] := by
    simpa [Transformer.vcg] using zeroBalance_effect visibleDb
  rw [hConst] at hEffect
  injection hEffect with hLocalDb
  subst hLocalDb
  rfl

theorem zeroBalance_preserves_invariant :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances zeroBalanceGuarantee
      0 Database.uniqueIds zeroBalanceInsertBody).preservesInvariant := by
  intro db db' hDb hGuarantee
  subst hGuarantee
  exact nonnegativeBalances_flush_zeroBalanceRow hDb

theorem zeroBalanceInsert_valid :
    Logic.GlobalValid nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      zeroBalanceGuarantee
      nonnegativeBalances := by
  exact Transformer.vcg_sound_false 0 Database.uniqueIds zeroBalanceInsertBody
    zeroBalance_effect_defined
    zeroBalance_guarantee_ok
    zeroBalance_preserves_invariant

theorem zeroBalance_symbolicVcg_shape (visibleDb : Database) :
    Transformer.symbolicVcg nonnegativeBalances "__inv" 0 zeroBalanceInsertBody visibleDb =
      some
        (SetLanguage.weakenToInvariant "__inv"
          (Transformer.assertionFormula nonnegativeBalances)
          (SetLanguage.singleton zeroBalanceRow)) := by
  simp [Transformer.symbolicVcg, Transformer.weakenSetEffect, zeroBalance_setEffect]

theorem zeroBalance_symbolicVcg_overapprox (visibleDb : Database)
    (hInv : nonnegativeBalances visibleDb) :
    Transformer.overapproximatesRows
      (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        (SetLanguage.singleton zeroBalanceRow))
      [zeroBalanceRow] := by
  exact Transformer.symbolicVcg_overapprox_sound
    nonnegativeBalances
    "__inv"
    0
    zeroBalanceInsertBody
    visibleDb
    [zeroBalanceRow]
    (SetLanguage.singleton zeroBalanceRow)
    hInv
    (zeroBalance_setEffect visibleDb)
    (by simpa [Transformer.vcg] using zeroBalance_effect visibleDb)

theorem zeroBalance_symbolicVcg_contains_row (visibleDb : Database)
    (hInv : nonnegativeBalances visibleDb) :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        (SetLanguage.singleton zeroBalanceRow))
      zeroBalanceRow := by
  exact zeroBalance_symbolicVcg_overapprox visibleDb hInv zeroBalanceRow (by simp)

def zeroBalanceWriteMembership : FirstOrder.MembershipFormula :=
  Option.get! (FirstOrder.inferWriteMembership 0 [] "x" zeroBalanceInsertBody)

theorem zeroBalance_inferWriteMembership :
    FirstOrder.inferWriteMembership 0 [] "x" zeroBalanceInsertBody =
      some zeroBalanceWriteMembership := by
  unfold zeroBalanceWriteMembership
  simp [FirstOrder.inferWriteMembership, zeroBalanceInsertBody, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_inferWriteMembership_contains_row (visibleDb : Database) :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem "x" zeroBalanceRow)
      zeroBalanceWriteMembership := by
  have hSound :=
    FirstOrder.inferWriteMembership_sound 0 [] "x" zeroBalanceInsertBody
      zeroBalanceWriteMembership visibleDb [zeroBalanceRow] zeroBalanceRow
      zeroBalance_inferWriteMembership
      (by simpa [Transformer.vcg] using zeroBalance_effect visibleDb)
  exact hSound.2 (by simp)

def interestBaseRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 4)]⟩

def interestBaseRow : Row :=
  Row.fromInsert 0 interestBaseRecord

def interestUpdatedRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 5)]⟩

def interestUpdatedRow : Row :=
  interestBaseRow.overwrite 1 interestUpdatedRecord

def addInterestBody : Semantics.Program :=
  .select "selected" "r"
    (.binop .eq (.proj (.var "r") "id") (.int 1))
    (.foreach (.var "selected") "done" "acct"
      (.update "r"
        (.withUpdates (.var "r")
          [("bal", .binop .add (.proj (.var "acct") "bal") (.int 1))])
        (.binop .eq (.proj (.var "r") "id") (.proj (.var "acct") "id"))))

def addInterestTxn : Semantics.Program :=
  .txn 1 Database.snapshotIsolation addInterestBody

def addInterestSetExpr : SetLanguage.SetExpr :=
  Option.get! (Transformer.inferSetEffect 1 [] addInterestBody [interestBaseRow])

theorem interestBase_nonnegative :
    nonnegativeBalances [interestBaseRow] := by
  intro row hMem
  rcases List.mem_singleton.mp hMem with rfl
  simp [interestBaseRow, interestBaseRecord, Row.fromInsert, RecordLit.lookup?]

theorem addInterest_effect :
    Transformer.inferEffect 1 [] addInterestBody [interestBaseRow] = some [interestUpdatedRow] := by
  native_decide

theorem addInterest_inferable :
    Transformer.SetInferable addInterestBody := by
  simp [Transformer.SetInferable, addInterestBody]

theorem addInterest_setEffect :
    Transformer.inferSetEffect 1 [] addInterestBody [interestBaseRow] = some addInterestSetExpr := by
  apply Transformer.option_eq_some_get!
  intro hNone
  rcases Transformer.inferSetEffect_some_of_inferEffect_some
      1 [] addInterestBody [interestBaseRow] [interestUpdatedRow]
      addInterest_inferable addInterest_effect with ⟨s, hSet⟩
  rw [hNone] at hSet
  cases hSet

theorem addInterest_symbolicVcg_shape :
    Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody [interestBaseRow] =
      some
        (SetLanguage.weakenToInvariant "__inv"
          (Transformer.assertionFormula nonnegativeBalances)
          addInterestSetExpr) := by
  simp [Transformer.symbolicVcg, Transformer.weakenSetEffect, addInterest_setEffect]

theorem addInterest_symbolicVcg_overapprox :
    Transformer.overapproximatesRows
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        addInterestSetExpr)
      [interestUpdatedRow] := by
  exact Transformer.symbolicVcg_overapprox_sound
    nonnegativeBalances
    "__inv"
    1
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    addInterestSetExpr
    interestBase_nonnegative
    addInterest_setEffect
    addInterest_effect

theorem addInterest_symbolicVcg_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        addInterestSetExpr)
      interestUpdatedRow := by
  exact addInterest_symbolicVcg_overapprox interestUpdatedRow (by simp)

theorem addInterest_symbolicVcg_contains_updatedRow_direct :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get! (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody [interestBaseRow]))
      interestUpdatedRow := by
  exact Transformer.symbolicVcg_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_symbolicVcgForTxn_info :
    ∃ info, Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn = some info := by
  refine ⟨Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody, ?_⟩
  simp [Transformer.symbolicVcgForTxn, addInterestTxn]

theorem addInterest_symbolicVcgForTxn_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get!
        ((Option.get! (Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn))
          [interestBaseRow]))
      interestUpdatedRow := by
  have hInfo :
      Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn =
        some (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody) := by
    simp [Transformer.symbolicVcgForTxn, addInterestTxn]
  exact Transformer.symbolicVcgForTxn_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    Database.snapshotIsolation
    addInterestBody
    (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody)
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    hInfo
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_symbolicPostForTxn_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get! (Transformer.symbolicPostForTxn nonnegativeBalances "__inv" addInterestTxn [interestBaseRow]))
      interestUpdatedRow := by
  exact Transformer.symbolicPostForTxn_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    Database.snapshotIsolation
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_rowPredicateFO_holds :
    FirstOrder.denote
      (DbAppProgramLogic.Env.insert [] "r" (.record interestBaseRecord))
      (FirstOrder.rowPredicateFormula [] "r"
        (.binop .eq (.proj (.var "r") "id") (.int 1))) := by
  rw [FirstOrder.denote_rowPredicateFormula]
  native_decide

def addInterestUpdateEnv : DbAppProgramLogic.Env :=
  [("acct", .record interestBaseRecord)]

def addInterestUpdateExpr : Expr :=
  .withUpdates (.var "r")
    [("bal", .binop .add (.proj (.var "acct") "bal") (.int 1))]

def addInterestUpdatePredicate : Expr :=
  .binop .eq (.proj (.var "r") "id") (.proj (.var "acct") "id")

theorem addInterest_updateMembershipFO_holds :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      (FirstOrder.encodeUpdateMembership
        "x" 1 addInterestUpdateEnv "r" addInterestUpdateExpr addInterestUpdatePredicate) := by
  have hNe : ("x" : VarName) ≠ "r" := by
    decide
  rw [FirstOrder.encodeUpdateMembership_sound
    "x" 1 addInterestUpdateEnv "r" addInterestUpdateExpr addInterestUpdatePredicate
    [interestBaseRow] interestUpdatedRow hNe]
  simp [Transformer.updateSetExpr, Transformer.updateSetExprWith, Transformer.rowPredicateFormula,
    SetLanguage.denote, SetLanguage.empty, addInterestUpdateEnv, addInterestUpdateExpr,
    addInterestUpdatePredicate, interestBaseRow, interestBaseRecord, interestUpdatedRow,
    interestUpdatedRecord, Row.fromInsert, Row.overwrite, RecordLit.lookup?]
  refine ⟨interestBaseRow, ?_, ?_, ?_⟩
  · simp [SetLanguage.Env.ofDatabases]
    rfl
  · native_decide
  · have hLookup :
        (((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "r" interestBaseRow).bindElem
          (Transformer.defaultOutVar "r") interestUpdatedRow).lookupElem? "r" = some interestBaseRow := by
      simp [Transformer.defaultOutVar, SetLanguage.Env.lookupElem?, SetLanguage.Env.lookupElemList?,
        SetLanguage.Env.bindElem]
    have hExists :
        ∃ updated,
          Expr.eval
              (Semantics.instantiateRecord "r" interestBaseRow.visible
                (Transformer.instantiateExpr addInterestUpdateEnv ["r"] addInterestUpdateExpr)) =
            some (.record updated) ∧
          interestUpdatedRow = interestBaseRow.overwrite 1 updated := by
      refine ⟨interestUpdatedRecord, ?_, ?_⟩
      · native_decide
      · simp [interestUpdatedRow, interestUpdatedRecord, interestBaseRow, Row.overwrite]
    simpa [hLookup] using hExists

def addInterestFullMembership : FirstOrder.MembershipFormula :=
  Option.get! (FirstOrder.inferMembershipFull 1 [] "x" addInterestBody [interestBaseRow])

theorem addInterest_membershipEncodable :
    FirstOrder.MembershipEncodable "x" addInterestBody := by
  simp [FirstOrder.MembershipEncodable, addInterestBody]

theorem addInterest_inferMembershipFull :
    FirstOrder.inferMembershipFull 1 [] "x" addInterestBody [interestBaseRow] =
      some addInterestFullMembership := by
  apply Transformer.option_eq_some_get!
  intro hNone
  rcases FirstOrder.inferMembershipFull_some_of_inferEffect_some
      1 [] "x" addInterestBody [interestBaseRow] [interestUpdatedRow]
      addInterest_membershipEncodable addInterest_effect with ⟨φ, hFormula⟩
  rw [hNone] at hFormula
  cases hFormula

theorem addInterest_inferMembershipFull_contains_updatedRow :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      addInterestFullMembership := by
  have hSound :=
    FirstOrder.inferMembershipFull_sound 1 [] "x" addInterestBody [interestBaseRow]
      addInterestFullMembership [interestUpdatedRow] interestUpdatedRow
      addInterest_inferMembershipFull addInterest_effect
  exact hSound.2 (by simp)

theorem addInterest_fullMembership_matches_setEffect :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      addInterestFullMembership ↔
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      addInterestSetExpr
      interestUpdatedRow := by
  exact FirstOrder.inferMembershipFull_matches_inferSetEffect
    1 [] "x" addInterestBody [interestBaseRow]
    addInterestFullMembership
    addInterestSetExpr
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferMembershipFull
    addInterest_setEffect
    addInterest_effect

theorem zeroBalance_singletonMembershipFO_holds :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] []).bindElem "x" zeroBalanceRow)
      (FirstOrder.encodeSingletonMembership "x" zeroBalanceRow) := by
  rw [FirstOrder.encodeSingletonMembership_denote]
  simp [SetLanguage.denote, SetLanguage.singleton]

end Examples

end DbAppProgramLogic
