module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBoundStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | exact GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExist
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem lens_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO :=
  @PositivityTheory.HtPt.Rc.lens

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypePolynomialVanishingCriterion
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block

theorem sum_eq_sum_subtype {α β : Type} [Fintype α] [AddCommMonoid β] (D : α → Prop)
    [Fintype {s // D s}] (G : α → β) (h : ∀ s, ¬ D s → G s = 0) :
    ∑ s, G s = ∑ s : {s // D s}, G s.1 := by
  classical
  rw [← Finset.sum_filter_of_ne (p := D) (fun x _ hx => by_contra fun hD => hx (h x hD))]
  exact Finset.sum_subtype _ (fun x => by simp) G

section

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem mem_freeLattice {S : Type} {a : S → w.valuationSubring} {r : ℕ} {x : S → Fin r → C} :
    x ∈ freeLattice a r ↔ ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
      x s i = ((f.eval (a s) : w.valuationSubring) : C) := Iff.rfl

def valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)) :
    Submodule w.valuationSubring ((E →+* C) → w.valuationSubring) :=
  Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)

theorem mul_mem_valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    {f g : (E →+* C) → w.valuationSubring} (hf : f ∈ valSpan emb) (hg : g ∈ valSpan emb) :
    f * g ∈ valSpan emb := by
  unfold valSpan at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    induction hg using Submodule.span_induction with
    | mem y h =>
      obtain ⟨b, rfl⟩ := h
      exact Submodule.subset_span ⟨a * b, by funext s; simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable {M : Type} [AddCommGroup M] [Module C M] [Module w.valuationSubring M]
  [IsScalarTower w.valuationSubring C M] {ρ : 𝓞 E →+* Module.End C M}
  {X : Submodule w.valuationSubring M} {N : ℕ} {t : Fin N → M}

theorem rho_mem (h : HT.IsFreeOn ρ X t) (a : 𝓞 E) (j : Fin N) : ρ a (t j) ∈ X := by
  have e := congrArg (fun u => ρ u (t j)) ((RingOfIntegers.basis E).sum_repr a)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply] at e
  rw [← e]
  refine sum_mem fun k _ => zsmul_mem ?_ _
  rw [h.2.2]
  exact Submodule.subset_span ⟨(j, k), rfl⟩

theorem eigCoord_mem (s : E →+* C) (v : Fin N → C) : eigCoord ρ t s v ∈ HT.eigSp ρ s := by
  rw [eigCoord_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ s _)

theorem exists_coord (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (h : HT.IsFreeOn ρ X t) {y : M} (hy : y ∈ X) :
    ∃ F : Fin N → (E →+* C) → w.valuationSubring, (∀ j, F j ∈ valSpan emb) ∧
      ∀ s, HT.eigProj ρ s y = ∑ j, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
  classical
  rw [h.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hx
    refine ⟨fun i s => if i = j then emb s (RingOfIntegers.basis E k) else 0, fun i => ?_,
      fun s => ?_⟩
    · by_cases hij : i = j
      · simp only [hij, if_true]
        exact Submodule.subset_span ⟨_, rfl⟩
      · simp only [hij, if_false]
        exact zero_mem (valSpan emb)
    · rw [HodgeDeterminantLattice.eigProj_act, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp [hemb]
  | zero => exact ⟨0, fun _ => zero_mem _, fun s => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    refine ⟨F + G, fun j => add_mem (hF j) (hG j), fun s => ?_⟩
    simp [e s, e' s, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    refine ⟨c • F, fun j => Submodule.smul_mem _ c (hF j), fun s => ?_⟩
    rw [← algebraMap_smul C c x, map_smul, e s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    rfl

theorem sum_smul_mem [CharZero C] [Fintype (E →+* C)]
    (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (hcard : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (h : HT.IsFreeOn ρ X t) (j : Fin N) {F : (E →+* C) → w.valuationSubring}
    (hF : F ∈ valSpan emb) :
    ∑ s, ((F s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X := by
  unfold valSpan at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have e : ∑ s : E →+* C, ((emb s a : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        ρ a (t j) := by
      have h1 := congrArg (fun T : Module.End C M => T (ρ a (t j)))
        (HT.sum_eigProj_eq_one C M E ρ hcard)
      simp only [LinearMap.sum_apply, HodgeDeterminantLattice.eigProj_act, Module.End.one_apply] at h1
      simpa only [hemb] using h1
    simpa only [e] using rho_mem h a j
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, AddMemClass.coe_add, add_smul, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ s : E →+* C, (((c • x) s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        c • ∑ s : E →+* C, ((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← algebraMap_smul C c (((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)), smul_smul]
      rfl
    rw [e]
    exact Submodule.smul_mem _ c hx

end

theorem block_freeLattice : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  intro E _ _ C _ _ w _ emb hemb hcard D π H M _ _ _ _ ρ X N t hfree _
  classical
  have hind : (fun s => if D s then (1 : w.valuationSubring) else 0) ∈ valSpan emb :=
    (H _ (fun s hs => if_neg hs)).1 ⟨1, fun s hs => by simp [hs]⟩
  have hpoly : ∀ F ∈ valSpan emb, ∃ g : Polynomial w.valuationSubring,
      ∀ s, D s → F s = g.eval (emb s π) := by
    intro F hF
    have hm := mul_mem_valSpan emb hind hF
    obtain ⟨g, hg⟩ := (H _ (fun s hs => by simp [hs])).2 hm
    exact ⟨g, fun s hs => by simpa [hs] using hg s hs⟩
  refine ⟨fun f => ⟨fun hx => ?_, fun hf => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hx
    have hD : ∀ s : {s // D s}, HT.eigProj ρ s.1 (∑ s, eigCoord ρ t s.1 (f s)) =
        eigCoord ρ t s.1 (f s) := by
      intro s
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single s]
      · exact HT.LatBasic.eigProj_of_mem (eigCoord_mem _ _)
      · intro s' _ hne
        exact HT.LatBasic.eigProj_of_ne (fun e => hne (Subtype.ext e.symm)) (eigCoord_mem _ _)
      · simp
    have hnD : ∀ s, ¬ D s → HT.eigProj ρ s (∑ s, eigCoord ρ t s.1 (f s)) = 0 := by
      intro s hs
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun s' _ =>
        HT.LatBasic.eigProj_of_ne (fun e : s = s'.1 => hs (by rw [e]; exact s'.2)) (eigCoord_mem _ _)
    have hF0 : ∀ j s, ¬ D s → F j s = 0 := by
      intro j s hs
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s hfree)
        (fun j => ((F j s : w.valuationSubring) : C)) (by rw [← e s, hnD s hs]) j
      exact Subtype.ext h1
    have hcoord : ∀ (s : {s // D s}) j, f s j = ((F j s.1 : w.valuationSubring) : C) := by
      intro s j
      have h0 := (hD s).symm.trans (e s.1)
      rw [eigCoord_apply] at h0
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s.1 hfree)
        (fun j => f s j - ((F j s.1 : w.valuationSubring) : C))
        (by simp only [sub_smul, Finset.sum_sub_distrib, h0, sub_self]) j
      exact sub_eq_zero.1 h1
    refine mem_freeLattice.2 fun j => ?_
    obtain ⟨g, hg⟩ := (H (F j) (hF0 j)).2 (hF j)
    exact ⟨g, fun s => by rw [hcoord s j, hg s.1 s.2]⟩
  · choose g hg using mem_freeLattice.1 hf
    let F : Fin N → (E →+* C) → w.valuationSubring :=
      fun j s => if D s then (g j).eval (emb s π) else 0
    have hFm : ∀ j, F j ∈ valSpan emb := fun j =>
      (H (F j) (fun s hs => if_neg hs)).1 ⟨g j, fun s hs => if_pos hs⟩
    have key : ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X :=
      sum_mem fun j _ => sum_smul_mem emb hemb hcard hfree j (hFm j)
    have e : ∑ s, eigCoord ρ t s.1 (f s) =
        ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      simp only [eigCoord_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_eq_sum_subtype D _ (fun s hs => by simp [F, hs])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [F, if_pos s.2, hg j s]
    rw [e]
    exact key
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hy
    refine ⟨fun s j => ((F j s.1 : w.valuationSubring) : C), mem_freeLattice.2 fun j => ?_,
      fun s => ?_⟩
    · obtain ⟨g, hg⟩ := hpoly _ (hF j)
      exact ⟨g, fun s => by rw [hg s.1 s.2]⟩
    · rw [e, eigCoord_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEigenSubDegreeEq
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.ConjEq

theorem eq_zero_of_scale {S : Type} [Finite S] (h : S → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (H : ∀ s, ∃ u, h u = p * h s) (s : S) : h s = 0 := by
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun s => |h s|)
  obtain ⟨u, hu⟩ := H m
  have h1 : |h u| = p * |h m| := by
    rw [hu, abs_mul, Nat.abs_cast]
  have h2 : |h u| ≤ |h m| := hm u
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have h4 : |h m| = 0 := by
    have h5 : 0 ≤ |h m| := abs_nonneg _
    nlinarith
  have h6 : |h s| ≤ 0 := h4 ▸ hm s
  exact abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))

variable {K : Type} [Field K]

theorem eig_star {O V : Type} [CommRing O] [StarRing O] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ χ' : O → K) (h : ∀ a, χ' a = χ (star a)) :
    eig (fun a => ρ (star a)) χ = eig ρ χ' := by
  ext x
  simp only [eig, Submodule.mem_iInf]
  constructor
  · intro H a
    have := H (star a)
    rwa [star_star, ← h] at this
  · intro H a
    have := H (star a)
    rwa [h, star_star] at this

section Data

variable (C : ACurve K) {p : ℕ} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (D : ConjData C p O d)

theorem lie_hom (a : O) : IsHom C D.lie D.lie (Matrix.toLin' (D.ρ a)) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  refine (D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩
  simpa using D.ρH_fst a y

theorem dual_bun : IsBun C (dotDual C D.lie) :=
  (deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1

variable {k S : Type} [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k))

theorem hodge_eq (hχ : IsSplit χ) (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t : S)
    (hst : ∀ a, χ t a = χ s (star a)) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))) =
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  classical
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _)
    (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH
    (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge
    (fun a x => by simpa using (D.ρH_inr a x).symm) (fun a y => by simpa using D.ρH_fst a y) s
  have h2 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h3 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, h2, h3]
  ring

theorem conj_eq [Fact p.Prime] [CharP K p] (hχ : IsSplit χ)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t u : S)
    (hst : ∀ a, χ t a = χ s (star a)) (hu : ∀ a, χ u a = χ s a ^ p) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ u a))) =
      p * (subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a)))) := by
  classical
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie))
    D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH
    (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj
    (fun a x => by simpa using D.α_act a x) (fun a y => by simpa using D.β_act a y) u
  have hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p := by
    funext a
    rw [hu, map_pow]
  have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))
  have h3 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose)
    (fun a => algebraMap k K (χ s a))
  have h4 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h5 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]
  ring

end Data

theorem subDeg_eig_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  intro K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst
  have hp : p.Prime := Fact.out
  haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hall := (isSplit_injective_and_exists O k S χ hχ).2
  have hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a) := fun s => by
    obtain ⟨t, ht⟩ := hall ((χ s).comp (starRingEnd O))
    exact ⟨t, fun a => by rw [ht]; rfl⟩
  have hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p := fun s => by
    obtain ⟨u, hu⟩ := hall ((frobenius k p).comp (χ s))
    exact ⟨u, fun a => by rw [hu]; rfl⟩
  have hzero := eq_zero_of_scale
    (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))))
    p hp.two_le (fun s => by
      obtain ⟨t, ht⟩ := hconj s
      obtain ⟨u, hu⟩ := hfrob s
      refine ⟨u, ?_⟩
      rw [conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s
  have h := hodge_eq C D χ hχ hk s t hst
  rw [hzero] at h
  exact sub_eq_zero.1 h.symm

end GlobalTheory.CompanionTheory.Ar.Crv.ConjEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEmbeddingsValuationRankBound
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red

section Xfer

variable {A B K M : Type} [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]

def xfer (h : (algebraMap A K).range = (algebraMap B K).range) (X : Submodule A M) : Submodule B M where
  carrier := X
  zero_mem' := X.zero_mem
  add_mem' := fun hx hy => X.add_mem hx hy
  smul_mem' := fun c x hx => by
    obtain ⟨a, ha⟩ : algebraMap B K c ∈ (algebraMap A K).range := h ▸ ⟨c, rfl⟩
    have e : c • x = a • x := by rw [← algebraMap_smul K c x, ← ha, algebraMap_smul]
    rw [e]
    exact X.smul_mem a hx

theorem mem_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {X : Submodule A M} {y : M} :
    y ∈ xfer h X ↔ y ∈ X := Iff.rfl

theorem xfer_span (h : (algebraMap A K).range = (algebraMap B K).range) (s : Set M) :
    xfer h (Submodule.span A s) = Submodule.span B s := by
  apply le_antisymm
  · intro y hy
    exact (Submodule.span_le (p := xfer h.symm (Submodule.span B s))).2
      (fun z hz => Submodule.subset_span hz) hy
  · exact Submodule.span_le.2 fun z hz => Submodule.subset_span hz

end Xfer

section XferEig

variable {A B K M : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]
  {E : Type} [Field E] [NumberField E]

theorem xfer_eigSub (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigSub ρ σ X) = HT.eigSub ρ σ (xfer h X) := by
  ext y
  exact Iff.rfl

theorem xfer_eigQuot (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigQuot ρ σ X) = HT.eigQuot ρ σ (xfer h X) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isFreeOn_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {ρ : 𝓞 E →+* Module.End K M}
    {X : Submodule A M} {N : ℕ} {t : Fin N → M} (hf : HT.IsFreeOn ρ X t) :
    HT.IsFreeOn ρ (xfer h X) t := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  rw [← xfer_span h, ← hf.2.2]

end XferEig

theorem targetV : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  intro hO E _ _ V C _ _ _ _ _ _ _ bar σ σ' rk p q ν hν hℓ hs hcard hσ' hbar
  have hr : (algebraMap V C).range = (algebraMap ν.valuationSubring C).range := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨_, (Valuation.mem_valuationSubring_iff _ _).2 (hν.map_le_one a)⟩, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨a, ha⟩ := hν.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 o.2)
      exact ⟨a, ha⟩
  obtain ⟨γ, hγ, H⟩ := hO E C ν bar σ σ' rk p q hℓ (fun s a => by
    obtain ⟨o, ho⟩ : s (a : E) ∈ (algebraMap ν.valuationSubring C).range := hr ▸ hs s a
    rw [← ho]
    exact o.2) hcard hσ' hbar
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  letI : Module ν.valuationSubring W := Module.compHom W (algebraMap ν.valuationSubring C)
  haveI : IsScalarTower ν.valuationSubring C W := ⟨fun o c y => by
    change ((o : C) * c) • y = (o : C) • (c • y)
    rw [mul_smul]⟩
  obtain ⟨ε, hε⟩ := H W ρ ρH (xfer hr HV) (xfer hr Lie) x v w u A h1 h2
    (by
      ext y
      rw [mem_xfer, ← h3]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩)
    (fun φ => by
      rw [mem_xfer, h4, ← hr]
      exact Iff.rfl)
    (isFreeOn_xfer hr h5) h6 h7
    (by rw [← xfer_span hr, h8, xfer_eigSub]) h9
    (by rw [← xfer_span hr, h10, xfer_eigSub]) h11 h12
    (by rw [← xfer_span hr, h13, xfer_eigQuot])
  obtain ⟨a, ha⟩ : algebraMap ν.valuationSubring C (ε : ν.valuationSubring) ∈ (algebraMap V C).range :=
    hr ▸ ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : algebraMap ν.valuationSubring C ((ε⁻¹ : (ν.valuationSubring)ˣ) : ν.valuationSubring) ∈
      (algebraMap V C).range := hr ▸ ⟨_, rfl⟩
  have hab : a * b = 1 := by
    apply hν.hom_inj
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  rw [hε]
  exact congrArg (· * γ) ha.symm

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red
end
end

