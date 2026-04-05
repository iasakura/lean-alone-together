# VCG を使った最小の検証例

この文書は、「VCG がどんな検証条件を出し、それを Lean でどう証明するか」を最短で見るためのメモです。

最初に読む場所は [Examples.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean) の `zeroBalance` 節です。

## 1. VCG object を作る

まず、transaction body に対して concrete VCG を作ります。

- [zeroBalanceInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

これは

```lean
Transformer.vcg R I G txnId isolation body
```

を具体化したものです。

`TransactionVCG` の field は [Transformer.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean) の `TransactionVCG` にあります。

- `effect`
- `execStable`
- `commitStable`
- `guaranteeOk`
- `preservesInvariant`

`vcg_sound_false` を使う最小例では、実際に自分で証明するのは次の 3 つです。

- `effectDefinedOn`
- `guaranteeOk`
- `preservesInvariant`

## 2. effect を計算する

この例では body は単純な `insert` なので、`effect` は 1 行で具体値まで計算できます。

- [zeroBalance_effect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

ここでやっていることは

- `vcg.effect visibleDb` を展開する
- `inferEffect` を `simp` で計算する
- レコード式の評価だけ `rw [zeroBalance_insert_eval]` で終わらせる

というだけです。

## 3. 定義域条件を証明する

VCG soundness の最初の side condition は

- [zeroBalance_effect_defined](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

です。

意味は:

- invariant `I` を満たす visible DB なら
- `effect visibleDb = some localDb` となる local write-set が存在する

この例では `zeroBalance_effect visibleDb` がすでに具体的なので、そのまま witness に `[zeroBalanceRow]` を出しています。

## 4. guarantee condition を証明する

次が

- [zeroBalance_guarantee_ok](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

です。

意味は:

- `effect visibleDb = some localDb`
- なら `flush localDb visibleDb` が保証 relation `G` を満たす

この例では `localDb` が必ず `[zeroBalanceRow]` であることを `zeroBalance_effect` から取り出して、`rfl` で終わっています。

## 5. invariant preservation を証明する

最後が

- [zeroBalance_preserves_invariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

です。

意味は:

- `I db`
- `G db db'`
- なら `I db'`

この例では `G` が `db' = flush [zeroBalanceRow] db` なので、既存補題 `nonnegativeBalances_flush_zeroBalanceRow` に還元しています。

## 6. soundness を呼ぶ

以上の 3 条件が揃ったら、

- [zeroBalanceInsert_valid_via_info](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

で

```lean
Transformer.vcg_sound_false ...
```

を 1 回呼べば `Logic.GlobalValid` が出ます。

## 7. どこを見ると一般形が分かるか

`vcg_sound_false` とその一般版はここです。

- [vcg_sound_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)
- [vcg_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

`vcg_sound_false` は no-rely case 用の最短 API です。  
実際の proof authoring を見るには、まず `zeroBalance` を真似して obligation を 3 本立てるのが一番分かりやすいです。

## 7.5. server/refinement 層へ持ち上げる

single transaction については、no-rely VCG 証明をそのまま server-facing な仕様へ持ち上げる薄い橋を
[Refinement.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Refinement.lean) に入れています。

- [handlerRefines_of_vcg_sound_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Refinement.lean)
- [txnParallelValid_exact_of_vcg_sound_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Refinement.lean)
- [txnCommitLog_exact_of_vcg_sound_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Refinement.lean)

`zeroBalance` ではこの橋をそのまま使っています。

- [zeroBalanceTxn_parallelValid_exact_via_vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L411)
- [zeroBalanceTxn_commitLog_via_vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L422)

つまり、最小の流れは

1. `vcg_sound_false` 用の 3 obligation を証明する
2. `Refinement.txnParallelValid_exact_of_vcg_sound_false` で exact commit spec つきの `ParallelValid` を得る
3. `Refinement.txnCommitLog_exact_of_vcg_sound_false` で実行 prefix を commit log として読む

です。`par` 合成では追加の rely 仮定が要るので、`vcg_sound_false` だけでは足りませんが、single
transaction を spec / commit-log に接続する最短ルートとしてはこれが今の標準形です。

## 8. read/write 例も見る

同じファイルの `addInterest` 節には、`select + foreach + update` を含む read/write transaction の
VCG object が入っています。

- [addInterestInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)
- [addInterest_effect_via_info](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)
- [addInterest_effect_defined_on_base](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)
- [addInterest_guarantee_on_base](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)
- [addInterest_preserves_invariant_on_base](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

こちらは `zeroBalance` のような full `vcg_sound_false` まで一気に進む例ではなく、

- concrete input `[interestBaseRow]` に対する `effect`
- その flush が chosen guarantee に一致すること
- concrete post-state が invariant を満たすこと

をそのまま Lean で書いています。`insert` だけでなく read/write の場合に、どこで record
lookup や `flush` の計算を手で支える必要があるかを見るのに向いています。
