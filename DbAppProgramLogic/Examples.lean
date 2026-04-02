import DbAppProgramLogic.Transformer

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

end Examples

end DbAppProgramLogic
