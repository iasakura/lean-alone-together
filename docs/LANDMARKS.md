# 重要な定義・定理のランドマーク

この文書は、「全部は読めないが、重要な定義と定理は押さえたい」という目的のためのノートです。  
各項目に、

- 直感
- 読み方
- 何が本質か
- 証明方針

を短く付けています。

## 1. `Command`
[Command](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Syntax.lean)

直感:
論文の言語 `T` です。ただし source term だけでなく runtime term も含みます。

読み方:

- `txn txnId isolation body`
  source の transaction
- `txnRuntime txnId isolation localDb snapshot body`
  実行中 transaction
- `par left right`
  並列合成

本質:
source syntax と runtime syntax を同じ datatype に入れているので、small-step semantics が直接書けます。

## 2. `Semantics.LocalStep`
[Semantics.LocalStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

直感:
transaction 本体だけの small-step semantics です。

読み方:

- 第一引数は transaction が今見ている DB
- `localDb` は未コミット delta

本質:
`select`, `insert`, `delete`, `update`, `foreach` は全部ここで動きます。global concurrency はまだ入っていません。

## 3. `Semantics.Step`
[Semantics.Step](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

直感:
top-level machine step です。

読み方:

- `txnStart`
  `txn` から `txnRuntime` へ
- `txnExec`
  runtime body を 1 step 進める
- `txnCommit`
  body が `skip` なら `flush`
- `parLeft` / `parRight`
  並列合成の片側を進める

本質:
actual machine step だけを表します。interference はまだありません。

## 4. `stableAssertion`, `stableBiAssertion`, `stableIsolation`
[stableAssertion](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
rely が入っても assertion / isolation 条件が壊れないことです。

読み方:

- `stableAssertion R P`
  `P` は global rely で保たれる
- `stableBiAssertion R P`
  `P` は localDb も見る
- `stableIsolation R I`
  isolation relation 自体が rely で分解可能

本質:
RG の side condition 本体です。`stableIsolation` は ordinary predicate ではなく 3 項 relation の stability なので、途中状態で分解できる形になっています。

## 5. `relyMod`
[relyMod](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
global rely を isolation guard で絞った local rely です。

読み方:

```lean
relyMod R I localDb visibleDb visibleDb'
```

は、

- `R visibleDb visibleDb'`
- ある `baseDb` があって
  - `I localDb baseDb visibleDb`
  - `I localDb baseDb visibleDb'`

を同時に要求します。

本質:
論文 Appendix B の `R modulo I` を Lean で表したものです。existential-witness 版になっています。

## 6. `localInterleavedStep`
[localInterleavedStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
local actual step と local rely step を混ぜた遷移です。

読み方:

- 左の disjunct
  `Semantics.LocalStep`
- 右の disjunct
  command と localDb は不変のまま visibleDb だけが rely で変わる

本質:
local proof は actual execution だけではなく interference つき trace に対して言われます。

## 7. `globalInterleavedStep`
[globalInterleavedStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
論文 Appendix C.2 に対応する top-level interleaving です。

読み方:

```lean
Semantics.Step ... ∨
(program' = program ∧ R globalDb globalDb')
```

本質:
rely step は outer DB だけを動かし、program はそのままです。ここが canonical な global semantics です。

## 8. `LocalValid`
[LocalValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
local judgment の意味論です。

読み方:
`P` が成り立つ状態から `c` を interleaving つきで実行して `skip` まで到達したら `Q` が成り立つ。

本質:
`LocalRG` の「本当の意味」です。

## 9. `GlobalValid`
[GlobalValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
top-level judgment の意味論です。

読み方:
2 成分あります。

- 終了時に `Ipost`
- 各 commit step が `G` を満たす

本質:
この開発では top-level correctness を「終了時の postcondition」だけでなく「commit ごとの spec」も含む形で見ています。

## 10. `LocalRG`
[LocalRG](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
Sec. 4 の local proof system です。

読み方:
constructor が proof rule です。`letE`, `ite`, `seq`, `select`, `insert`, `delete`, `update`, `foreach`, `conseq` が主な入口です。

本質:
ここを見ると、各構文を logic がどう扱うかが分かります。

証明方針:
`localRG_sound` は constructor ごとの帰納法です。

## 11. `GlobalRG`
[GlobalRG](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
top-level proof system です。

読み方:
主な constructor は `txn` と `conseq` です。

本質:
transaction-local proof と top-level invariant / guarantee をつなぐ場所です。一般の `par` rule はまだここにはありません。

## 12. `localRG_sound`
[localRG_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
local proof system は semantic に正しい。

読み方:

```lean
LocalRG ... P c Q → LocalValid ... P c Q
```

本質:
Theorem 4.3 の local 側です。

証明方針:
構文規則ごとの induction。難所は `seq` と `foreach` で、そのための multistep 分解補題が前半に入っています。

## 13. `globalRG_sound`
[globalRG_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

直感:
top-level RG proof system も semantic に正しい。

読み方:

```lean
GlobalRG ... I program G Ipost → GlobalValid ... I program G Ipost
```

本質:
Theorem 4.3 の global 側です。

証明方針:
芯は `txnRuntimeFwd_sound`, `txnProgramFwd_sound`, `txnGlobalValid_of_localValid` にあります。global execution を local proof に読み替えて closure しています。

## 14. `SetExpr`
[SetExpr](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)

直感:
論文 Fig. 7 の集合言語 `S` です。

読み方:
`localDb`, `globalDb`, `comprehension`, `bind`, `existsSet`, `ite`, `union` を見ます。

本質:
symbolic VCG が返す postcondition の object language です。

## 15. `denote`
[denote](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)

直感:
`SetExpr` の意味論です。

読み方:
`denote ρ s row` は、環境 `ρ` のもとで `row ∈ s` が成り立つことです。

本質:
symbolic soundness は最終的に concrete row と `denote` の一致になります。

## 16. `inferEffect`
[inferEffect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

直感:
transaction body の concrete effect 推論器です。

読み方:
`Database → Option Database` を返します。

本質:
proof engineering の主軸です。まずこれを semantics に結び、そのあと symbolic/FOL に持ち上げています。

## 17. `vcg`
[vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

直感:
transaction ごとの簡約版 VCG です。

読み方:
effect, commit stability, guarantee, invariant preservationを 1 つの record にまとめています。

本質:
いまの VCG は「effect inference + soundness bridge」として実装されています。

## 18. `inferSetEffect`
[inferSetEffect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

直感:
`SetExpr` を返す symbolic transformer です。

読み方:
`inferEffect` と同じ body から `Option SetExpr` を返します。

本質:
Fig. 8 に寄せた symbolic 層です。

## 19. `symbolicVcg`, `symbolicPostForTxn`
[symbolicVcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

直感:
弱化済み symbolic postcondition の入口です。

読み方:

- `symbolicVcg`
  body から weakened symbolic post を返す
- `symbolicPostForTxn`
  `txn` syntax まで含めた入口

本質:
`Examples.addInterest_*` を読むときの入口です。

## 20. `inferMembershipFull`
[inferMembershipFull](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/FirstOrder.lean)

直感:
transaction body を first-order membership formula に落とします。

読み方:
`x` という distinguished row variable を用意して、「この row が symbolic effect に属する条件」を式として返します。

本質:
Sec. 5.2 に向かう橋です。solver までの自動化ではありません。

## 21. `HandlerRefines`
[HandlerRefines](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

直感:
handler correctness の読みやすい別名です。

読み方:
中身は `GlobalValid` そのものです。

本質:
server 層は core logic を置き換えるのではなく、`GlobalValid` を handler/request 用語で読みやすくしているだけです。

## 22. `ProgramDone`, `TxnCommitStep`, `ParallelValid`
[ProgramDone](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

直感:
quiescent endpoint と commit event を server-style に読むための wrapper です。

読み方:

- `ProgramDone`
  `skip` と `par` の done closure
- `TxnCommitStep`
  nested `par` の中の commit を 1 つ拾う
- `ParallelValid`
  done endpoint の postconditionと各 commit の spec を同時に要求する

本質:
これは論文本体の追加層です。いまは単一 transaction を server-style spec に上げる最小の層だけが入っています。

## 23. `txnParallelValid_of_handlerRefines`
[txnParallelValid_of_handlerRefines](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

直感:
`HandlerRefines` を single-transaction の `ParallelValid` に持ち上げる補題です。

読み方:

```lean
HandlerRefines ... (.txn txnId isolation body) spec ...
→ ParallelValid ... (.txn txnId isolation body) (fun _ => spec) ...
```

本質:
server 層の最初の bridge です。一般の `par` rule ではなく、まず単一 handler の server-style 読み替えから始めています。

## 読み始めるならどれか

最短ルートは次です。

1. `Examples.zeroBalanceInsert_valid`
2. `Transformer.vcg_sound_false`
3. `Logic.GlobalValid`
4. `Logic.globalRG_sound`
5. `Semantics.Step`

symbolic/FOL 側を見たいなら次です。

1. `Examples.addInterest_symbolicVcg_contains_updatedRow`
2. `Transformer.symbolicVcg`
3. `Transformer.inferSetEffect`
4. `SetLanguage.denote`
5. `FirstOrder.inferMembershipFull`
