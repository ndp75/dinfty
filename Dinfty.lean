-- The root, and the default `lake build` target.
--
-- Every module in `Dinfty/` is reachable from here, so a bare `lake build`
-- compiles the whole project.  It used to import only `Dinfty.Formalization`,
-- which meant `lake build` compiled one module out of a hundred and seventy --
-- and that one the frozen legacy monolith that nothing else imports.
--
-- The two lists are exactly the roots of the import DAG; everything else is
-- pulled in transitively.  (A module docstring cannot go here: `/-! -/` is a
-- command, and commands may not precede `import`.)

-- NOT imported: Dinfty.Formalization.  The frozen legacy monolith is not merely
-- dead (nothing imports it) -- it is INCOMPATIBLE with the live split: it and
-- Dinfty.SierpinskiApplication both declare instPartialOrderScottEndPDBilimit,
-- so importing both fails with "environment already contains".  That is why the
-- root used to import the monolith and nothing else.  It is also the only module
-- in the project that declares axioms.  Build it on its own:
--     lake build Dinfty.Formalization

-- Result modules.

import Dinfty.EscapeAnalysis
import Dinfty.EscapeProof
import Dinfty.GasketCoreIFS
import Dinfty.GasketNotOpen
import Dinfty.GasketObstruction
import Dinfty.CodeB
import Dinfty.RhoContinuity
import Dinfty.AddressConvergence
import Dinfty.BilimitGap
import Dinfty.CopyIdeal
import Dinfty.SeamTriangle
import Dinfty.StageRigidity
import Dinfty.PhiStagePipe
import Dinfty.StageEmbedding
import Dinfty.EmbDImage
import Dinfty.LevelEmbNotGeneric
import Dinfty.EmbTagwise
import Dinfty.SeamFixed
import Dinfty.PatchedEmbedding
import Dinfty.StageCofinal
import Dinfty.AtomlessBilimit
import Dinfty.StageCover
import Dinfty.CanonicalChain
import Dinfty.SeamCut
import Dinfty.IdealInvariant
import Dinfty.QAAExplicit
import Dinfty.SigmaRebuild
import Dinfty.InternalIFSInstance
import Dinfty.Verify
