/-
  LambdaSat — ColoredEMatch: Color-Aware Pattern Matching
  Fase 15 Subfase 4: Layer 2 core operation.

  Extends the base e-matching (EMatch.lean) with color context.
  The key addition is the `colored_jump` instruction: when binding a
  pattern variable to an e-class, the colored e-match uses the color's
  compositeFind to get the canonical representative.

  This means:
  - Under color c, if classes A and B are merged, a pattern matching A
    will also find matches through B (and vice versa)
  - The base e-match is a special case (color = root)

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)

  Key results:
  - `coloredLookup`: look up a class under a color
  - `coloredSameClass`: check if two classes are equivalent under a color
  - `coloredSearchPattern`: pattern matching with colored class membership
  - `applyColoredRule`: apply a colored rewrite rule
-/
import LambdaSat.EMatch
import LambdaSat.ColorTypes
import LambdaSat.ColoredMerge

set_option autoImplicit false

namespace LambdaSat

variable {Op : Type} [BEq Op] [Hashable Op] [NodeOps Op]

/-! ## Colored Class Lookup -/

/-- Look up the canonical representative of a class under a color.
    This is the `colored_jump` instruction from Easter Egg. -/
def coloredLookup (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (c : ColorId) (classId : EClassId) (fuel : Nat := 100) : EClassId :=
  ColoredLayer.findUnderColor cl baseFind c classId fuel

/-- Two classes are in the same colored e-class if they have the same
    canonical representative under color c. -/
def coloredSameClass (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (c : ColorId) (a b : EClassId) (fuel : Nat := 100) : Bool :=
  coloredLookup cl baseFind c a fuel == coloredLookup cl baseFind c b fuel

/-! ## Colored Substitution -/

/-- Canonicalize a substitution under a color: map all bound ids to their
    color-canonical representatives. -/
def canonicalizeSubst (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (c : ColorId) (subst : Substitution) (fuel : Nat) : Substitution :=
  subst.toList.foldl (fun acc (v, id) =>
    acc.insert v (coloredLookup cl baseFind c id fuel)
  ) Substitution.empty

/-! ## Colored Search Pattern -/

/-- Search for matches of a pattern in the e-graph under a specific color.
    Uses the base ematch but canonicalizes the root class id under the color.

    `baseGraph` provides the structural information (which nodes exist).
    `cl` provides the color-specific merges. -/
def coloredSearchPattern (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId)
    (pat : Pattern Op) (rootId : EClassId)
    (fuel : Nat := 100) : MatchResult :=
  let canonRoot := coloredLookup cl baseFind c rootId fuel
  ematch baseGraph pat canonRoot

/-! ## Colored Rewrite Rule -/

/-- A colored rewrite rule: a rule that only applies under a specific color
    (assumption context). -/
structure ColoredRewriteRule (Op : Type) [BEq Op] [Hashable Op] where
  /-- The color (assumption) under which this rule applies -/
  color : ColorId
  /-- The base rewrite rule -/
  rule : RewriteRule Op

/-- Apply a colored rewrite rule at a specific class.
    The rule is applied in the base graph, but any resulting merge
    is performed in the colored layer (not the base graph). -/
def applyColoredRuleAt (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId)
    (crule : ColoredRewriteRule Op) (classId : EClassId)
    (fuel : Nat := 100) : ColoredLayer Op :=
  let canonId := coloredLookup cl baseFind crule.color classId fuel
  let matchResults := ematch baseGraph crule.rule.lhs canonId
  matchResults.foldl (fun acc subst =>
    match instantiate baseGraph crule.rule.rhs subst with
    | some (rhsId, _) =>
      (ColoredLayer.mergeUnderColor acc baseFind crule.color canonId rhsId fuel).1
    | none => acc
  ) cl

/-- Apply a colored rewrite rule to all classes in the e-graph. -/
def applyColoredRule (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId)
    (crule : ColoredRewriteRule Op) (fuel : Nat := 100) :
    ColoredLayer Op :=
  baseGraph.classes.toList.foldl (fun acc (classId, _) =>
    applyColoredRuleAt acc baseGraph baseFind crule classId fuel
  ) cl

/-- Apply a list of colored rewrite rules. -/
def applyColoredRules (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId)
    (crules : List (ColoredRewriteRule Op)) (fuel : Nat := 100) :
    ColoredLayer Op :=
  crules.foldl (fun acc crule =>
    applyColoredRule acc baseGraph baseFind crule fuel
  ) cl

/-! ## Properties -/

/-- Colored search at the root color canonicalizes via baseFind. -/
theorem coloredSearchPattern_root_canon (cl : ColoredLayer Op)
    (baseGraph : EGraph Op) (baseFind : EClassId → EClassId)
    (pat : Pattern Op) (rootId : EClassId) (fuel : Nat) :
    coloredSearchPattern cl baseGraph baseFind colorRoot pat rootId fuel =
    ematch baseGraph pat (coloredLookup cl baseFind colorRoot rootId fuel) := by
  rfl

/-! ## Smoke tests -/

private inductive CETestOp where
  | lit : Nat → CETestOp
  | add : EClassId → EClassId → CETestOp
  deriving BEq, Hashable

#eval
  let cl : ColoredLayer CETestOp := ColoredLayer.empty
  let (c1, cl1) := ColoredLayer.addColor cl colorRoot
  let baseFind := fun id => id
  let (cl2, _) := ColoredLayer.mergeUnderColor cl1 baseFind c1 5 10 100
  let same := coloredSameClass cl2 baseFind c1 5 10 100
  let notSame := coloredSameClass cl2 baseFind colorRoot 5 10 100
  s!"Under c1: 5≡10={same}. Under root: 5≡10={notSame}"

end LambdaSat
