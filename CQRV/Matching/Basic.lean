module

public import CQRV.Matching.Term
public import CQRV.Matching.Normalize
public import CQRV.Matching.Miller
public import CQRV.Matching.Lgg
public import CQRV.Matching.Library
public import CQRV.Matching.Hint

/-!
# CQRV.Matching

Report §4 — normalization, Miller-pattern matcher, anti-unification, repair hints. Pipeline
(report §4.1.1, §4.2.4, §4.3):

```
SigmaIn.toTerm : SigmaIn → Term                        -- ground σ_in, fixed field order
normalize      : Term → Term                           -- AC normal form (both φ and σ_in)
millerMatch    : Term → Term → Except MatchFailure Subst  -- Algorithm 1, empty or singleton
lgg            : Term → Term → Term × Subst × Subst    -- anti-unification, fresh Gᵢ
matchLibrary   : List LibEntry → Term → LibResult      -- Algorithm 2, early exit
renderHints    : Term → LibResult → List Hint          -- Table 4
```
No Physlib import in this component.
-/
