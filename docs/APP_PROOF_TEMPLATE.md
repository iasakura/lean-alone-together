# アプリケーション証明テンプレ

この文書は、`DbAppProgramLogic/AppWorkflowExample.lean` を雛形として、
自分のアプリケーションをどう証明していくかを手順化したものです。

`AppWorkflowExample.lean` は end-to-end の並列合成まで見せるため、transaction 自体は
event-sourced に寄せてあります。`select/update` を使う read/modify/write handler の VCG を
先に見たい場合は
[ReadWriteWorkflowExample.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/ReadWriteWorkflowExample.lean)
を先に見る方が自然です。

いまの tutorial の題材は、イベントソーシング風の小さな銀行 ledger です。

- 一方の transaction は「利息支払いイベント」を 1 件追加する
- もう一方の transaction は「出金イベント」を 1 件追加する

proof pattern 自体は、別のアプリでも同じです。

対象としている流れは次です。

1. アプリの transaction / handler を定義する
2. グローバル不変条件を決める
3. 各 transaction の rely / guarantee / abstract spec を決める
4. `Transformer.vcg` にかける
5. 出てきた verification condition を証明する
6. `vcg_sound` で handler refinement を得る
7. `||` で並列に合成した結果を request-level spec として読む

## 入口

まず読むべきファイルは:

- [AppWorkflowExample.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

です。`Examples.lean` は部品集として使い、実際の流れは `AppWorkflowExample.lean` を真似るのがよいです。

## 手順

### 1. transaction を定義する

最低限必要なのは:

- request の型
- 各 transaction body
- `txnId`
- parallel に並べたプログラム

`AppWorkflowExample.lean` の対応箇所:

- [Request](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [creditInterestBody](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [recordWithdrawalBody](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [ledgerProgram](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

### 2. グローバル不変条件を決める

ここで必要なのは「強い業務仕様」より、まず transaction 証明を支える小さな invariant です。

典型例:

- id の一意性
- 参照整合性
- 残高が非負
- レコード shape の健全性

対応箇所:

- [LedgerInvariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

### 3. abstract spec と rely を決める

各 transaction について:

- abstract state transformer `f`
- relational spec `StateSpec.graph f`
- 相手 transaction の spec を含む rely

を決めます。

対応箇所:

- [creditInterestSpec](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [recordWithdrawalSpec](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [creditInterestRely](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [recordWithdrawalRely](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

request-level に読みたいときは:

- `requestOfTxn`
- `requestApply`

もここで定義します。

### 4. VCG を作る

各 transaction body に対して

```lean
Transformer.vcg R I G txnId isolation body
```

を作ります。

対応箇所:

- [creditInterestInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [recordWithdrawalInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

## 5. verification condition を証明する

今回の VCG で主に埋めるものは:

- `guaranteeOk`
- `commitStable`
- `LocalValid ... effectPost ...`
- `preservesInvariant`

対応箇所:

  - 左 transaction:
  - [creditInterest_guarantee_ok](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [creditInterest_commitStable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [creditInterest_localValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [creditInterest_preserves_invariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- 右 transaction:
  - [recordWithdrawal_inferEffect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [recordWithdrawal_guarantee_ok](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [recordWithdrawal_commitStable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [recordWithdrawal_localValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
  - [recordWithdrawal_preserves_invariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

### ここで詰まりやすい点

素の VCG goal を毎回直接証明するのは、少し複雑になるとつらいです。通常は次の補題を先に立てます。

- `inferEffect` の計算結果を固定する補題
- `flush` が invariant を保つ補題
- rely 下の `LocalValid` を直接与える補題

`Examples.lean` の `zeroBalance_localValid_effectPost_readCommitted_of_stable` は、その典型です。

### 6. handler refinement を得る

verification condition が埋まったら `vcg_sound` を呼んで、transaction 単体の正しさを
server-facing な `HandlerRefines` に上げます。

対応箇所:

- [creditInterest_handlerRefines](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)
- [recordWithdrawal_handlerRefines](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

### 7. 並列合成する

最後に、2 transaction の handler refinement を並列に合成し、request-level の `foldl`
定理として読みます。

対応箇所:

- [ledgerProgram_request_foldl](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/AppWorkflowExample.lean)

この定理が言っているのは:

- 実装 program の finite parallel 実行があり
- commit された request 列を取り出すと
- 最終 DB は request-level abstract transformer の `foldl` で説明できる

ということです。

## 実際に自分のアプリへ移すときの最小 checklist

1. transaction body を Lean の `Semantics.Program` で書く
2. 小さい global invariant を決める
3. 各 transaction の abstract spec を `StateSpec.graph` か relation で書く
4. 相手 transaction の spec を rely に入れる
5. `Transformer.vcg` を定義する
6. `guaranteeOk`, `commitStable`, `LocalValid`, `preservesInvariant` を証明する
7. `vcg_sound` で `HandlerRefines` を得る
8. `Refinement.txnPair_request_foldl_of_handlerRefines` か同系の定理で並列結果を読む

## 次に作るべきもの

この template は 2 transaction の小例です。実アプリ向けには次の抽象化を足す価値があります。

- handler family をまとめる structure
- request family 全体に対する generic theorem
- handler-level の `P/Q` 仕様層
- model state と `Rep` を使う refinement 層

ただし、いまの repo でも「小さな finite parallel program が request-level の合成を実装する」
ところまではこの template で試せます。
