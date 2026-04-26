import DbAppProgramLogic.Transformer
import DbAppProgramLogic.Legacy.Transformer.Concrete
import DbAppProgramLogic.Legacy.Transformer.SetEffect
import DbAppProgramLogic.Legacy.Transformer.PaperEffect
import DbAppProgramLogic.Legacy.Transformer.Soundness

/-!
Legacy aggregator.

Files under `DbAppProgramLogic/Legacy/` belong to the older "concrete VCG" line of development
(`inferEffect`, `vcg_sound`, `symbolicVcg`, ...). They are *not* the paper-aligned formalization
that the rest of `DbAppProgramLogic/Transformer/` is being rebuilt around (Fig. 13 / Theorem C.18 of
`1710.09844v2.pdf`).

They are kept here, behind a separate aggregator, so that:

* downstream examples that depend on `vcg_sound` / `symbolicVcg` continue to build,
* and the main `DbAppProgramLogic.Transformer` aggregator stays focused on the paper-aligned files.

New developments should depend on `DbAppProgramLogic.Transformer` only. Importing
`DbAppProgramLogic.Legacy` should be considered a temporary measure pending full migration.
-/
