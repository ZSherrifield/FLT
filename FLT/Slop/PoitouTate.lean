/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.H1GSfinite
public import FLT.Slop.PoitouTate.actionof
public import FLT.Slop.PoitouTate.cupprod
public import FLT.Slop.PoitouTate.inflmap
public import FLT.Slop.PoitouTate.phipmap
public import FLT.Slop.PoitouTate.ConjInvariance
public import FLT.Slop.PoitouTate.LocalGlobalMaps
public import FLT.Slop.PoitouTate.DualModule
public import FLT.Slop.PoitouTate.LocalTateDuality
public import FLT.Slop.PoitouTate.InfRes
public import FLT.Slop.PoitouTate.PoitouTateStatement

/-!
# Poitou–Tate

Blueprint-driven scaffold of the Poitou–Tate nine-term exact sequence, following
`PTblueprint.tex` (deleted in commit `68f7a3f`; recover with
`git show 68f7a3f^:FLT/Slop/PoitouTate/PTblueprint.tex`). The headline statement is
`NumberField.PoitouTate.poitouTate` in `PoitouTateStatement.lean`.

See `FLT/Slop/PoitouTate/RECONCILIATION.md` for the reconciliation of this folder with the
`PoitouTateLogos.lean` draft and the plan for reaching a sorry-free statement with explicit
maps.
-/
