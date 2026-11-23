module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_target_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  first | (exact @GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (exact GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (intros; apply GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  first | (exact @GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (exact GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (intros; apply GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (exact GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.exists_isogTarget_of_dvr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pIsogenyTargets_at_charP_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (M : Model b N) (u : M.X), u ∉ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → ∀ (L : Type) [Field L] [IsAlgClosed L] (h : M.X.residueField u →+* L), {ζ : Sp L ⟶ M.X | CorrQF.IsogTarget M c (spMap h ≫ M.X.fromSpecResidueField u) ζ}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget <;> assumption)
end

