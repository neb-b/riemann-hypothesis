module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
section
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnimodOver

open Module

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_basis (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin _)
  exact ⟨_, b.ofZLatticeBasis ℝ Λ, b.ofZLatticeBasis_span ℝ Λ⟩

theorem discrete_dual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
  infer_instance

theorem discrete_of_le {L M : Submodule ℤ V} [DiscreteTopology M] (h : L ≤ M) :
    DiscreteTopology L :=
  DiscreteTopology.of_continuous_injective (continuous_inclusion h) (Set.inclusion_injective h)

theorem span_of_le {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono h

theorem exists_nsmul_mem {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by
  haveI := discrete_of_le h
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ M := ⟨span_of_le hs h⟩
  have hr : finrank ℤ (L.comap M.subtype) = finrank ℤ M := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, ZLattice.rank ℝ L, ZLattice.rank ℝ M]
  haveI hfin : Finite (M ⧸ L.comap M.subtype) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  refine ⟨Nat.card (M ⧸ L.comap M.subtype), Nat.card_pos, fun x hx => ?_⟩
  have h1 := (L.comap M.subtype).toAddSubgroup.nsmul_index_mem ⟨x, hx⟩
  exact h1

theorem exists_selfDual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by
  haveI := discrete_dual B hB Λ hs
  set D := B.dualSubmodule Λ with hD
  haveI : IsZLattice ℝ D := ⟨span_of_le hs hint⟩
  haveI : IsNoetherian ℤ D := inferInstance
  have anti : ∀ {L M : Submodule ℤ V}, L ≤ M → B.dualSubmodule M ≤ B.dualSubmodule L :=
    fun h _ hy x hx => hy x (h hx)
  obtain ⟨M, ⟨h1, h2⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2 this)
    {M : Submodule ℤ D | Λ ≤ M.map D.subtype ∧
      M.map D.subtype ≤ B.dualSubmodule (M.map D.subtype)}
    ⟨Λ.comap D.subtype, by
      simp only [Set.mem_setOf_eq, Submodule.map_comap_subtype, inf_eq_right.2 hint]
      exact ⟨le_rfl, hint⟩⟩
  refine ⟨M.map D.subtype, h1, Submodule.map_subtype_le _ _, le_antisymm ?_ h2⟩
  intro w hw
  have hwD : w ∈ D := anti h1 hw
  have hle : M ≤ M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := le_sup_left
  have heq : M = M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := by
    by_contra hne
    refine hmax _ ⟨h1.trans (Submodule.map_mono hle), ?_⟩ (lt_of_le_of_ne hle hne)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have e1 := h2 ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
    have e2 := hw _ ⟨y₁, hy₁, rfl⟩
    have e3 := hw _ ⟨x₁, hx₁, rfl⟩
    have e4 : B (x₁ : V) w = - B w (x₁ : V) := (hA.neg_eq _ _).symm
    have e5 : B w w = 0 := hA w
    have e6 : B (D.subtype (x₁ + a • ⟨w, hwD⟩)) (D.subtype (y₁ + c • ⟨w, hwD⟩)) =
        B (D.subtype x₁) (D.subtype y₁) + a • B w (D.subtype y₁) - c • B w (D.subtype x₁) := by
      simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, map_add (f := _), map_zsmul,
        LinearMap.add_apply, LinearMap.smul_apply, e4, e5, smul_zero, smul_neg, add_zero]
      ring
    rw [e6]
    exact sub_mem (add_mem e1 (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e3)
  have : (⟨w, hwD⟩ : D) ∈ M := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨_, this, rfl⟩

theorem dualSubmoduleToDual_surjective (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  have hbmem : ∀ i, b i ∈ Λ := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  intro φ
  set y : V := ∑ i, (φ ⟨b i, hbmem i⟩ : ℤ) • B.dualBasis hB b i with hy
  have hymem : y ∈ B.dualSubmodule Λ := by
    rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hLI : LinearIndependent ℤ b := b.linearIndependent.restrict_scalars' ℤ
  let bΛ : Module.Basis (Fin n) ℤ Λ := (Module.Basis.span hLI).map (LinearEquiv.ofEq _ _ hb)
  have hbΛ : ∀ i, (bΛ i : V) = b i := fun i => by simp [bΛ, Module.Basis.span_apply]
  refine ⟨⟨y, hymem⟩, bΛ.ext fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hspec := LinearMap.BilinForm.dualSubmoduleParing_spec B ⟨y, hymem⟩ (bΛ j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hspec
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply, hspec]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hbΛ, hy, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left, smul_ite, smul_zero, zsmul_eq_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 2
  exact Subtype.ext (hbΛ j).symm

theorem exists_unimodular (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by
  obtain ⟨M, h1, h2, h3⟩ := exists_selfDual B hB hA Λ hs hint
  haveI := discrete_dual B hB Λ hs
  haveI : DiscreteTopology M := discrete_of_le h2
  have hsM := span_of_le hs h1
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem hs h1
  let e := LinearEquiv.ofEq _ _ h3.symm
  refine ⟨M, N, (B.dualSubmoduleToDual M).comp e.toLinearMap, h1, hN, hNM, this, hsM, ?_, ?_⟩
  · intro a b
    exact B.dualSubmoduleParing_spec (e a) b
  · exact Function.Bijective.comp (g := B.dualSubmoduleToDual M) (f := e)
      ⟨B.dualSubmoduleToDual_injective hB M hsM, dualSubmoduleToDual_surjective B hB M hsM⟩
      e.bijective

end General

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun a b w => by simp [add_dotProduct])
    (fun r a w => by simp [smul_dotProduct])
    (fun a b w => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun r a w => by simp [Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem imForm_isAlt {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) :
    (imForm Hm).IsAlt := by
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  intro z
  rw [imForm_apply]
  have hq := key (star z)
  rw [star_star] at hq
  exact Complex.conj_eq_iff_im.mp hq

theorem imForm_nondegenerate {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    (imForm Hm).Nondegenerate := by
  have hL : ∀ z : Fin g → ℂ, (∀ w, imForm Hm z w = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz (Complex.I • z)
    rw [imForm_apply, star_smul, Complex.star_def, Complex.conj_I, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 := hp z hne
    simp [Complex.mul_im] at h1
    linarith
  have hR : ∀ w : Fin g → ℂ, (∀ z, imForm Hm z w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hw (Complex.I • w)
    rw [imForm_apply, smul_dotProduct, smul_eq_mul] at h1
    have h2 := hp w hne
    simp [Complex.mul_im] at h1
    linarith
  first
    | exact ⟨hL, hR⟩
    | exact hL

theorem exists_unimodular_overlattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  intro g Λ Hm hd hs hH hp hint
  obtain ⟨M, N, Ef, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_unimodular (imForm Hm) (imForm_nondegenerate hH hp) (imForm_isAlt hH) Λ hs
      (fun x hx y hy => by
        obtain ⟨n, hn⟩ := hint x hx y hy
        exact Submodule.mem_one.2 ⟨n, by rw [imForm_apply, hn]; simp⟩)
  refine ⟨M, N, Ef, h1, h2, fun x hx => ?_, h4, h5, h6, h7⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact h3 x hx

end GlobalTheory.UnimodOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCocycleStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    (∀ k j, GlobalTheory.SecGlue.IsCombIn (V j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ t k j)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k] ![algebraMap R (Localization.Away (f j * f k)) (f k) ^ N]) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    ∃ (M : ℕ) (t' : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
      (∀ k j, t' k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) ∧
      (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t' k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) ∧
      (∀ k j, t' k j ⁻¹ᵁ V j = ⊤) ∧
      ∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t' k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t' k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N + M)] := by
  first | exact @GlobalTheory.SecGlue.exists_pow_cocycle | exact GlobalTheory.SecGlue.exists_pow_cocycle | (intros; apply GlobalTheory.SecGlue.exists_pow_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRoots
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem mem_range_of_AIC_of_eval₂_eq_zero {T L : Type} [CommRing T] [CommRing L] [IsDomain L]
    (hA : AIC T) (f : T →+* L) (x : L) :
    ∀ (n : ℕ) (p : T[X]), p.natDegree = n → p.Monic → p.eval₂ f x = 0 → x ∈ Set.range f := by
  intro n
  haveI : Nontrivial T := f.domain_nontrivial
  induction n with
  | zero =>
    intro p hd hm hx
    have hp : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst hp
    simp at hx
  | succ n ih =>
    intro p hd hm hx
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hroot : IsRoot p a := ha
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hXm : (X - C a : T[X]).Monic := Polynomial.monic_X_sub_C a
    have hqm : q.Monic := by
      exact Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)
    have hqd : q.natDegree = n := by
      have h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree :=
        hXm.natDegree_mul hqm
      rw [hfac, hd, Polynomial.natDegree_X_sub_C] at h1
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨a, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
      exact (sub_eq_zero.mp h).symm
    · exact ih q hqd hqm h

theorem exists_retraction_of_AIC : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T]
    [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E],
    AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ →
    ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  intro D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD
  let π : E →ₐ[D] E ⧸ Q := Ideal.Quotient.mkₐ D Q
  let f : T →ₐ[D] E ⧸ Q := π.comp ι

  have hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := D)
    rw [← hQD]
    ext d
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap D T d) = 0 ↔ _
    rw [f.commutes]
    change algebraMap D (E ⧸ Q) d = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective f := by
    have := (RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker
    exact this

  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := D) e)
    have hmem := mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e)
      _ (p.map (algebraMap D T)) rfl (hpm.map _) (by
        rw [Polynomial.eval₂_map]
        have hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E) := by
          ext d
          simp only [RingHom.comp_apply, RingHom.coe_coe]
          rw [f.commutes]
          rfl
        rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero])
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  let eqv : T ≃ₐ[D] E ⧸ Q := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩
  · ext t
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]
    apply eqv.injective
    change eqv (eqv.symm (π (ι t))) = eqv t
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · ext e
    rw [RingHom.mem_ker]
    change eqv.symm (π e) = 0 ↔ e ∈ Q
    rw [AlgEquiv.symm_apply_eq, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJets
section
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by

  have hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q →
      ∀ k, k < n → coeff k p = coeff k q := by
    intro n p q h k hk
    have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
    rwa [map_sub, sub_eq_zero] at this

  have hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f) := by
    intro f k j hkj
    rcases Nat.lt_or_ge j k with h | h
    · have hk : k = j + 1 := by omega
      subst hk
      exact (hdv _ _ _ (hc j f) (j + 1) (by omega)).symm
    · induction j, h using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        rw [hdv _ _ _ (hc j f) k (by omega)]
        exact ih (by omega)
  let g : A → PowerSeries R := fun f => PowerSeries.mk fun k => coeff k (φ k f)
  have hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f) := by
    intro f k j hkj
    simp only [g, PowerSeries.coeff_mk]
    exact (hstab f k j hkj).symm
  have gmul : ∀ f h, g (f * h) = g f * g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hg f x.1 k (by omega), hg h x.2 k (by omega)]
  have gadd : ∀ f h, g (f + h) = g f + g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add (f := _), map_add (f := _),
      hg f k k (by omega), hg h k k (by omega)]
  have gone : g 1 = 1 := by
    ext k
    rw [hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]
  have gzero : g 0 = 0 := by
    have := gadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let γ : A →+* PowerSeries R :=
    { toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · ext b k
    show coeff k (g (π b)) = coeff k (C (β b))
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]
  · ext f
    show constantCoeff (g f) = β (ε f)
    rw [← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply,
      (hφ 0).2.2.1 f]
  · intro f
    show coeff 1 (g f) = δ f
    rw [hg f 1 0 (by omega), (hφ 0).2.2.2 f]
  · ext f k
    show coeff k (rescale 2 (g f)) = coeff k (g (m f))
    rw [coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega),
      hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionVirtualCharacterPrime
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
namespace GlobalTheory.Shin

theorem tensorInd_virt_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hp hs χ hχ
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    exact mem_zpowers_of_prime_card rfl hs
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G χ).1 hχ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb
  obtain ⟨Z, hZ, hZ1, hZ2⟩ := GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b
    ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩)
    ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (_root_.GlobalTheory.BI.isChar_zero_and_add ℂ ℂ G).1, by simp⟩)
  have hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hA
  have hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hB
  refine ⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩
  · intro g
    simp only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]
    ring
  · intro δ
    simp only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGContinuousInv
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem expG_continuous_inv : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z →
    Continuous (fun t : ℝ => expG ε Z t) ∧
      ∀ t : ℝ, toM (expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  refine ⟨(Formalism.REAL.group_exponential_facts n ε Z hZ).2.2.1, fun t => ?_⟩
  have hmul : toM (expG ε Z t) * NormedSpace.exp (-((t : ℂ) • Z)) = 1 := by
    rw [Formalism.REAL.toM_expG ε Z t hZ]
    have h := Formalism.REAL.one_parameter_subgroup_holds n Z t (-t)
    have e : ((-t : ℝ) : ℂ) • Z = -((t : ℂ) • Z) := by push_cast; rw [neg_smul]
    rw [e, add_neg_cancel] at h
    simpa using h.symm
  exact Units.inv_eq_of_mul_eq_one_right hmul

end GlobalTheory
end

