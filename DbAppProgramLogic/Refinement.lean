import DbAppProgramLogic.Legacy
import DbAppProgramLogic.Server

namespace DbAppProgramLogic

/-!
Thin bridges from transaction-local VCG proofs to the server-facing refinement layer.

The core transaction logic still lives in `Logic`/`Transformer`. This file only packages common
"single verified transaction" patterns so examples and downstream applications can move directly
from VCG obligations to handler/server specifications.
-/

namespace Refinement

/-- A no-rely VCG proof immediately gives a server-facing handler refinement judgment. -/
theorem handlerRefines_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Server.HandlerRefines I (fun _ _ => False) (.txn txnId isolation body) G I := by
  exact Transformer.vcg_sound_false txnId isolation body hDefined hGuarantee hPreserve

/-- The same VCG proof can be re-exported as a server-level validity judgment with one exact
commit specification attached to the concrete transaction id. -/
theorem txnParallelValid_exact_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Server.ParallelValid I (fun _ _ => False) (.txn txnId isolation body)
      (Server.ExactTxnSpec txnId G) I := by
  refine Server.txnParallelValid_of_handlerRefines_at
    (txnId := txnId)
    (isolation := isolation)
    (body := body)
    (spec := G)
    (specs := Server.ExactTxnSpec txnId G)
    ?_
    ?_
  · intro db db' hSpec
    exact ⟨rfl, hSpec⟩
  · exact handlerRefines_of_vcg_sound_false txnId isolation body hDefined hGuarantee hPreserve

/-- In the closed-system case, the exact server validity judgment yields a concrete commit log for
any reachable execution prefix of the single transaction. -/
theorem txnCommitLog_exact_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant)
    {db : Database} (hDb : I db)
    {finalCfg : GlobalConfig}
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨(.txn txnId isolation body), db⟩ finalCfg) :
    ∃ events,
      Server.CommitLog (Server.ExactTxnSpec txnId G) db events finalCfg.globalDb := by
  exact Server.parallelValid_commitLog_of_silentRely
    (txnParallelValid_exact_of_vcg_sound_false txnId isolation body
      hDefined hGuarantee hPreserve)
    (fun db db' hFalse => False.elim hFalse)
    hDb
    hRun

/-- The abstract transformer family induced by a verified two-transaction parallel program. Only
the two concrete transaction ids perform state changes; all other ids act as identity. -/
def txnPairFs
    (leftTxnId : TxnId) (leftF : StateTransformer)
    (rightTxnId : TxnId) (rightF : StateTransformer) :
    TxnId → StateTransformer :=
  fun txnId =>
    if txnId = leftTxnId then
      leftF
    else if txnId = rightTxnId then
      rightF
    else
      id

/-- Two handler refinements with graph specs package into a graph-valued `ParallelValid` judgment
for the pair. -/
theorem txnPair_parallelValid_graph_of_handlerRefines
    {I : Assertion} {R : Rely}
    {leftTxnId rightTxnId : TxnId}
    (hDistinct : leftTxnId ≠ rightTxnId)
    {leftIsolation rightIsolation : IsolationSpec Database}
    {leftBody rightBody : Semantics.Program}
    {leftF rightF : StateTransformer}
    (hLeft :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph rightF db db')
        (.txn leftTxnId leftIsolation leftBody)
        (StateSpec.graph leftF)
        I)
    (hRight :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph leftF db db')
        (.txn rightTxnId rightIsolation rightBody)
        (StateSpec.graph rightF)
        I) :
    Server.ParallelValid I R
      (.par
        (.txn leftTxnId leftIsolation leftBody)
        (.txn rightTxnId rightIsolation rightBody)
        : Semantics.Program)
      (fun txnId => StateSpec.graph (txnPairFs leftTxnId leftF rightTxnId rightF txnId))
      I := by
  refine Server.parallelValid_of_specSubset
    (Server.txnPair_parallelValid_of_handlerRefines hLeft hRight)
    ?_
  intro txnId db db' hSpec
  rcases hSpec with hLeftSpec | hRightSpec
  · rcases hLeftSpec with ⟨rfl, hGraph⟩
    simpa [StateSpec.graph, txnPairFs]
      using hGraph
  · rcases hRightSpec with ⟨rfl, hGraph⟩
    have hNe : txnId ≠ leftTxnId := by
      intro hEq
      exact hDistinct hEq.symm
    simpa [StateSpec.graph, txnPairFs, if_neg hNe]
      using hGraph

/-- Closed-system two-transaction executions can be read back as a fold over the two abstract
state transformers in commit order. -/
theorem txnPair_foldl_of_handlerRefines
    {I : Assertion} {R : Rely}
    {leftTxnId rightTxnId : TxnId}
    (hDistinct : leftTxnId ≠ rightTxnId)
    {leftIsolation rightIsolation : IsolationSpec Database}
    {leftBody rightBody : Semantics.Program}
    {leftF rightF : StateTransformer}
    (hLeft :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph rightF db db')
        (.txn leftTxnId leftIsolation leftBody)
        (StateSpec.graph leftF)
        I)
    (hRight :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph leftF db db')
        (.txn rightTxnId rightIsolation rightBody)
        (StateSpec.graph rightF)
        I)
    (hSilent : Server.SilentRely R)
    {db : Database} (hDb : I db)
    {finalCfg : GlobalConfig}
    (hRun :
      Logic.GlobalMultiStep R
        ⟨(.par
            (.txn leftTxnId leftIsolation leftBody)
            (.txn rightTxnId rightIsolation rightBody)
            : Semantics.Program), db⟩
        finalCfg) :
    ∃ commits,
      finalCfg.globalDb =
        List.foldl
          (fun current txnId =>
            txnPairFs leftTxnId leftF rightTxnId rightF txnId current)
          db
          commits := by
  rcases Server.parallelValid_foldl_of_graphSpecs
      (txnPair_parallelValid_graph_of_handlerRefines hDistinct hLeft hRight)
      hSilent
      hDb
      hRun with
    ⟨commits, _hSeq, hFold⟩
  exact ⟨commits, hFold⟩

/-- Request-indexed variant of `txnPair_foldl_of_handlerRefines`. The two verified handlers are
read back as a fold over committed requests. -/
theorem txnPair_request_foldl_of_handlerRefines
    {Req : Type} {I : Assertion} {R : Rely}
    {leftTxnId rightTxnId : TxnId}
    {leftIsolation rightIsolation : IsolationSpec Database}
    {leftBody rightBody : Semantics.Program}
    {requestOf : TxnId → Req} {fs : RequestTransformer Req}
    (hLeft :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph (fs (requestOf rightTxnId)) db db')
        (.txn leftTxnId leftIsolation leftBody)
        (StateSpec.graph (fs (requestOf leftTxnId)))
        I)
    (hRight :
      Server.HandlerRefines I
        (fun db db' => R db db' ∨ StateSpec.graph (fs (requestOf leftTxnId)) db db')
        (.txn rightTxnId rightIsolation rightBody)
        (StateSpec.graph (fs (requestOf rightTxnId)))
        I)
    (hSilent : Server.SilentRely R)
    {db : Database} (hDb : I db)
    {finalCfg : GlobalConfig}
    (hRun :
      Logic.GlobalMultiStep R
        ⟨(.par
            (.txn leftTxnId leftIsolation leftBody)
            (.txn rightTxnId rightIsolation rightBody)
            : Semantics.Program), db⟩
        finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl
          (fun current req => fs req current)
          db
          (Server.CommitLog.requests requestOf events) := by
  have hPar :
      Server.ParallelValid I R
        (.par
          (.txn leftTxnId leftIsolation leftBody)
          (.txn rightTxnId rightIsolation rightBody)
          : Semantics.Program)
        (Server.CombinedSpecs
          (Server.ExactTxnSpec leftTxnId (StateSpec.graph (fs (requestOf leftTxnId))))
          (Server.ExactTxnSpec rightTxnId (StateSpec.graph (fs (requestOf rightTxnId)))))
        I := by
    exact Server.txnPair_parallelValid_of_handlerRefines hLeft hRight
  have hPar' :
      Server.ParallelValid I R
        (.par
          (.txn leftTxnId leftIsolation leftBody)
          (.txn rightTxnId rightIsolation rightBody)
          : Semantics.Program)
        (RequestSpec.graphAssign requestOf fs)
        I := by
    refine Server.parallelValid_of_specSubset hPar ?_
    intro txnId db db' hSpec
    rcases hSpec with hLeftSpec | hRightSpec
    · rcases hLeftSpec with ⟨rfl, hGraph⟩
      simpa [RequestSpec.graphAssign, RequestSpec.assign, StateSpec.graph]
        using hGraph
    · rcases hRightSpec with ⟨rfl, hGraph⟩
      simpa [RequestSpec.graphAssign, RequestSpec.assign, StateSpec.graph]
        using hGraph
  rcases Server.parallelValid_request_foldl_of_graphAssign
      hPar'
      hSilent
      hDb
      hRun with
    ⟨events, _hLog, hFold⟩
  exact ⟨events, hFold⟩

end Refinement

end DbAppProgramLogic
