module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumEqAlternatingSum
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem finsum_mem_finset_sum_comm {α β : Type} (s : Set α) (P : Finset β) (f : β → α → ℚ)
    (hf : ∀ p ∈ P, (s ∩ Function.support (f p)).Finite) :
    ∑ᶠ x ∈ s, ∑ p ∈ P, f p x = ∑ p ∈ P, ∑ᶠ x ∈ s, f p x := by
  classical
  have hU : (⋃ p ∈ (P : Set β), s ∩ Function.support (f p)).Finite :=
    Set.Finite.biUnion P.finite_toSet fun p hp => hf p (Finset.mem_coe.1 hp)
  have key : ∀ g : α → ℚ, (∀ x ∈ s, g x ≠ 0 → x ∈ ⋃ p ∈ (P : Set β), s ∩ Function.support (f p)) →
      ∑ᶠ x ∈ s, g x = ∑ x ∈ hU.toFinset, g x := by
    intro g hg
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨hx, hgx⟩; exact ⟨hg x hx hgx, hgx⟩
    · rintro ⟨hx, hgx⟩
      obtain ⟨p, _, hxs, _⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨hxs, hgx⟩
  rw [key]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => (key _ ?_).symm
    intro x hx h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, h⟩
  · intro x hx h
    obtain ⟨p, hp, hpx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, hpx⟩

theorem HH_eq_alternating_GG : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u →
    HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  intro K B ι _ _ e π S hL hF I hI u hu
  have hPlus : ∀ J ⊆ S, B.Plus (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ B.Plus (fun a b ha hb => ⟨ha.1.mul hb.1, by rw [map_mul, ha.2, hb.2]⟩)
      ⟨isUnit_one, map_one _⟩ (fun j hj => (hF.2 j (hJ hj)).1)
  have heta1 : K.eta 1 = 1 := by
    have h := eta_mul (K := K) (x := 1) (y := 1) one_ne_zero one_ne_zero
    have h2 := eta_sq (K := K) 1
    rw [mul_one] at h
    rw [← h] at h2
    exact h2
  have heta : ∀ J : Finset ι, J ⊆ S → K.eta (Algebra.norm K.E (∏ j ∈ J, π j)) = (-1 : ℚ) ^ J.card := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro _; simp [heta1]
    | insert a J ha ih =>
      intro hJ
      have haS : a ∈ S := hJ (Finset.mem_insert_self a J)
      have hJS : J ⊆ S := (Finset.subset_insert a J).trans hJ
      rw [Finset.prod_insert ha, map_mul,
        eta_mul ((hF.2 a haS).1.1.map (Algebra.norm K.E)).ne_zero
          ((hPlus J hJS).1.map (Algebra.norm K.E)).ne_zero,
        ih hJS, (hF.2 a haS).2.2, Finset.card_insert_of_notMem ha, pow_succ]
      ring
  have hterm0 : ∀ w s M, term B π ∅ ∅ w s M = indM B M w * indD B M s := by
    intro w s M; simp [term, dlt]
  have hHG : ∀ v, HH B π ∅ ∅ v 1 = B.GG v := by
    intro v
    unfold HH InvAlg.GG
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun M => ?_
    have hD : InDual B 1 M ↔ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range := by
      simp only [InDual, one_mul]
    simp only [Set.indicator, Set.mem_setOf_eq, hterm0, indM, indD, ← hD]
    by_cases h1 : M ∈ B.Lin
    · by_cases h2 : v ∈ M
      · by_cases h3 : InDual B 1 M
        · rw [if_pos h1, if_pos h2, if_pos h3, if_pos ⟨h1, h2, hD.1 h3⟩]; ring
        · rw [if_pos h1, if_pos h2, if_neg h3, if_neg (fun h => h3 (hD.2 h.2.2))]; ring
      · rw [if_pos h1, if_neg h2, zero_mul, mul_zero]
        exact (if_neg (fun h => h2 h.2.1)).symm
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  have hexp : HH B π I (S \ I) u 1 = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) := by
    have h1 : ∀ M, B.sgnLat M * term B π I (S \ I) u 1 M = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
        (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
          (B.sgnLat M * term B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) M) := by
      intro M
      rw [Finset.sum_product, term, dlt, dlt, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [hterm0]; ring
    unfold HH
    simp_rw [h1]
    rw [finsum_mem_finset_sum_comm]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_finsum_mem]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
      refine (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K B ι e π S hL.2 hF ∅ ∅ (Finset.empty_subset _) (Finset.empty_subset _) _ _
        ((hPlus p.1 (hp.1.trans hI)).1.mul hu) ((hPlus p.2 (hp.2.trans Finset.sdiff_subset)).1.mul isUnit_one)).subset ?_
      rintro M ⟨hM, hne⟩
      refine ⟨hM, fun h => hne ?_⟩
      simp only [h, mul_zero]
  rw [hexp]
  have hstep : ∀ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
      (-1 : ℚ) ^ ((p.1 ∪ p.2) ∩ I).card * B.GG ((∏ j ∈ p.1 ∪ p.2, π j) * u) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have hdisj : Disjoint p.1 p.2 := Finset.disjoint_left.2 fun x h1 h2 =>
      (Finset.mem_sdiff.1 (hp.2 h2)).2 (hp.1 h1)
    have hcap : (p.1 ∪ p.2) ∩ I = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (Finset.mem_sdiff.1 (hp.2 h)).2
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    have hy := hPlus p.2 (hp.2.trans Finset.sdiff_subset)
    have hm := _root_.GlobalTheory.UnitLemma.Move.HH_mul_unit K B ι π ∅ ∅ ((∏ j ∈ p.1, π j) * u) 1 (∏ j ∈ p.2, π j) hL hy
    have hsq := eta_sq (K := K) (Algebra.norm K.E (∏ j ∈ p.2, π j))
    have hm' : HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
        K.eta (Algebra.norm K.E (∏ j ∈ p.2, π j)) *
          HH B π ∅ ∅ ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)) 1 := by
      rw [hm, ← mul_assoc, hsq, one_mul]
    rw [hm', heta p.2 (hp.2.trans Finset.sdiff_subset), hHG, hcap, Finset.prod_union hdisj]
    have h11 : ((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card) = 1 := by rw [← mul_pow]; norm_num
    calc (-1 : ℚ) ^ p.1.card * (-1) ^ p.2.card *
          ((-1) ^ p.2.card * B.GG ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)))
        = (-1 : ℚ) ^ p.1.card * B.GG ((∏ j ∈ p.1, π j) * (∏ j ∈ p.2, π j) * u) *
          (((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card)) := by ring_nf
      _ = _ := by rw [h11, mul_one]
  rw [Finset.sum_congr rfl hstep]
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun J => (J ∩ I, J \ I)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    rw [Finset.mem_powerset]
    exact Finset.union_subset (hp.1.trans hI) (hp.2.trans Finset.sdiff_subset)
  · intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hJ le_rfl⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have h2 : ∀ x ∈ p.2, x ∉ I := fun x hx => (Finset.mem_sdiff.1 (hp.2 hx)).2
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (h2 x h)
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (hp.1 h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, h2 x h⟩
  · intro J _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · intro p _
    rfl

end GlobalTheory.UnitLemma.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactors
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem abs_sgnLat {K : UQ} (B : InvAlg K) (M : Submodule K.O B.A) : |B.sgnLat M| = 1 := by
  unfold InvAlg.sgnLat
  exact abs_eta _

theorem isUnit_alg {K : UQ} (B : InvAlg K) {a : K.O} (ha : a ≠ 0) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (IsUnit.mk0 _ ?_)
  intro h
  exact ha ((IsFractionRing.injective K.O K.E) (by rw [h, map_zero]))

variable {ι₁ ι₂ : Type} (S₁ : Finset ι₁) (S₂ : Finset ι₂) (L k : ℕ) (p : ι₁ ⊕ ι₂ → ℤ)

theorem win_inl (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win S₁ ∅ L k (p ∘ Sum.inl) := by
  intro i
  obtain ⟨h1, h2, h3, _⟩ := h (Sum.inl i)
  exact ⟨h1, h2, fun hi => h3 (by simpa using hi), fun hi => absurd hi (Finset.notMem_empty _)⟩

theorem win_inr (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win ∅ S₂ L k (p ∘ Sum.inr) := by
  intro j
  obtain ⟨h1, h2, _, h4⟩ := h (Sum.inr j)
  exact ⟨h1, h2, fun hj => absurd hj (Finset.notMem_empty _), fun hj => h4 (by simpa using hj)⟩

theorem win_of (h₁ : Win S₁ ∅ L k (p ∘ Sum.inl)) (h₂ : Win ∅ S₂ L k (p ∘ Sum.inr)) :
    Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
  rintro (i | j)
  · obtain ⟨a1, a2, a3, _⟩ := h₁ i
    exact ⟨a1, a2, fun hi => a3 (by simpa using hi), fun hi => by simp at hi⟩
  · obtain ⟨a1, a2, _, a4⟩ := h₂ j
    exact ⟨a1, a2, fun hj => by simp at hj, fun hj => a4 (by simpa using hj)⟩

theorem mid_inl (h : Mid (S₁.disjSum S₂) L k p) : Mid S₁ L k (p ∘ Sum.inl) :=
  fun i hi => h (Sum.inl i) (by simpa using hi)

theorem mid_inr (h : Mid (S₁.disjSum S₂) L k p) : Mid S₂ L k (p ∘ Sum.inr) :=
  fun j hj => h (Sum.inr j) (by simpa using hj)

end GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.ProdSum Polynomial Filter Topology

theorem GlobalTheory.UnitLemma.Desc.hh_prod_tendsto : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  classical
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) :=
      LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  have hsB : (B₁.prod B₂).P.Separable := hP ▸ hsep
  have hs₁ : B₁.P.Separable := hL₁.2
  have hs₂ : B₂.P.Separable := hL₂.2
  have hF := _root_.GlobalTheory.UnitLemma.Desc.isFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.UnitLemma.Desc.exists_pos K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF
  have hIS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hI'S : S₂.map Function.Embedding.inr ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hcov : ∀ i ∈ S₁.disjSum S₂, i ∈ S₁.map Function.Embedding.inl ∨ i ∈ S₂.map Function.Embedding.inr := by
    rintro (i | j) h <;> simp_all
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.UnitLemma.Desc.term_window K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF _ _ hIS hI'S hcov N 1 1
    isUnit_one isUnit_one
  obtain ⟨L₁, hL₁'⟩ := _root_.GlobalTheory.UnitLemma.Desc.term_window K B₁ ι₁ e₁ π₁ S₁ a hs₁ ha hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _)
    (fun i hi => Or.inl hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨L₂, hL₂'⟩ := _root_.GlobalTheory.UnitLemma.Desc.term_window K B₂ ι₂ e₂ π₂ S₂ a hs₂ ha hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl
    (fun i hi => Or.inr hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℕ → Submodule K.O B₁.A → ℚ, ∀ k M,
      φ₁ k M = B₁.sgnLat M * term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : ℕ → Submodule K.O B₂.A → ℚ, ∀ k M,
      φ₂ k M = B₂.sgnLat M * term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      g k M = (B₁.prod B₂).sgnLat M * term (B₁.prod B₂)
        (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      f k M = g k M - K.eta (resultant B₁.P B₂.P) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) :=
    ⟨_, fun _ _ => rfl⟩
  have hfinB : ∀ k, {M ∈ (B₁.prod B₂).Lin | g k M ≠ 0}.Finite := fun k =>
    (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ hsB hF _ _ hIS hI'S
      (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 ((isUnit_alg (B₁.prod B₂) ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hg, h, mul_zero])⟩)
  have hfin₁ : ∀ k, {M ∈ B₁.Lin | φ₁ k M ≠ 0}.Finite := fun k =>
    (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K B₁ ι₁ e₁ π₁ S₁ hs₁ hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _) _ _
      ((isUnit_alg B₁ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₁, h, mul_zero])⟩)
  have hfin₂ : ∀ k, {M ∈ B₂.Lin | φ₂ k M ≠ 0}.Finite := fun k =>
    (_root_.GlobalTheory.UnitLemma.Desc.finite_term_ne_zero K B₂ ι₂ e₂ π₂ S₂ hs₂ hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl _ _
      ((isUnit_alg B₂ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₂, h, mul_zero])⟩)
  have hsum : ∀ k, ∑ᶠ M ∈ (B₁.prod B₂).Lin, f k M =
      HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 -
      (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
        (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) := by
    intro k
    obtain ⟨hfinP, hfib⟩ := _root_.GlobalTheory.UnitLemma.FibSum.fibsum K B₁ B₂ hL₁.1 hL₂.1 hsep (φ₁ k) (φ₂ k) (hfin₁ k) (hfin₂ k)
    have e1 : ∀ M, f k M = g k M + (-K.eta (resultant B₁.P B₂.P)) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) := by
      intro M; rw [hf]; ring
    rw [finsum_mem_congr rfl (fun M _ => e1 M)]
    rw [finsum_mem_add_distrib' ?_ ?_, ← mul_finsum_mem, hfib]
    · have h0 : ∑ᶠ M ∈ (B₁.prod B₂).Lin, g k M = HH (B₁.prod B₂)
          (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hg k M
      have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ k M = HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₁ k M
      have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ k M = HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₂ k M
      rw [h0, h1, h2]
      unfold UQ.eta
      rw [neg_eq_neg_one_mul (K.q : ℚ), mul_zpow]
      ring
    · exact (hfinB k).subset (fun M ⟨hM, hne⟩ => ⟨hM, hne⟩)
    · exact hfinP.subset (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by simp only [h, mul_zero])⟩)
  have hbound : ∀ k M, |f k M| ≤ 2 ^ (S₁.map (@Function.Embedding.inl ι₁ ι₂)).card * 2 ^ (S₂.map (@Function.Embedding.inr ι₁ ι₂)).card +
      2 ^ S₁.card * 2 ^ (∅ : Finset ι₁).card * (2 ^ (∅ : Finset ι₂).card * 2 ^ S₂.card) := by
    intro k M
    rw [hf, hg, hφ₁, hφ₂]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_sgnLat, one_mul]; exact abs_term _ _ _ _ _ _ _
    · rw [abs_mul, abs_eta, one_mul, abs_mul, abs_mul, abs_mul, abs_sgnLat, abs_sgnLat, one_mul, one_mul]
      exact mul_le_mul (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _) (abs_nonneg _) (by positivity)
  have hsupp : ∀ k, max L₀ (max L₁ L₂) ≤ k → ∀ M ∈ (B₁.prod B₂).Lin, ∀ p,
      Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p →
      f k M ≠ 0 → Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (max L₀ (max L₁ L₂)) k p ∧
        ¬ Mid (S₁.disjSum S₂) (max L₀ (max L₁ L₂)) k p := by
    intro k hk M hM p hp hne
    set L := max L₀ (max L₁ L₂) with hL
    have tp := _root_.GlobalTheory.UnitLemma.Desc.pos_term_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p (algebraMap K.O B₁.A a ^ (2 * k))
      (algebraMap K.O B₂.A a ^ (2 * k))
    obtain ⟨hp₁, hp₂⟩ := tp.1 hp
    have a0 := hL₀ L (le_max_left _ _) k hk M p hp
    have a1 := hL₁' L (le_trans (le_max_left _ _) (le_max_right _ _)) k hk _ _ hp₁
    have a2 := hL₂' L (le_trans (le_max_right _ _) (le_max_right _ _)) k hk _ _ hp₂
    rw [one_mul] at a0 a1 a2
    have hwin : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
      by_cases h0 : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M = 0
      · have hne' := hne
        rw [hf, hg, hφ₁, hφ₂, h0] at hne'
        have t1 : term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        have t2 : term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        exact win_of S₁ S₂ L k p (a1.1 t1) (a2.1 t2)
      · exact a0.1 h0
    refine ⟨hwin, fun hmid => hne ?_⟩
    have e0 := a0.2 hwin hmid
    have e1 := a1.2 (win_inl S₁ S₂ L k p hwin) (mid_inl S₁ S₂ L k p hmid)
    have e2 := a2.2 (win_inr S₁ S₂ L k p hwin) (mid_inr S₁ S₂ L k p hmid)
    have hA : (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) =
        ((algebraMap K.O B₁.A a ^ (2 * k), algebraMap K.O B₂.A a ^ (2 * k)) : B₁.A × B₂.A) :=
      Prod.ext (by simp) (by simp)
    have key : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M =
        term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) *
        term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      rw [e1, e2]
      refine Eq.trans e0 (Eq.trans ?_ tp.2)
      congr 2
    rw [hf, hg, hφ₁, hφ₂, key, _root_.GlobalTheory.UnitLemma.SgnProd.sgnLat_prod K B₁ B₂ hsep M hM]
    ring
  have hc := _root_.GlobalTheory.UnitLemma.Desc.tendsto_badWindow_div_rho K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF (S₁.map Function.Embedding.inl)
    (S₂.map Function.Embedding.inr) hcov N (max L₀ (max L₁ L₂)) _ f hN hbound hsupp
  refine hc.congr (fun k => ?_)
  rw [hsum k]
  have hA' : (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      ((algebraMap K.O B₁.A a ^ k, algebraMap K.O B₂.A a ^ k) : B₁.A × B₂.A) :=
    Prod.ext (by simp) (by simp)
  have hr : (B₁.prod B₂).rho (algebraMap K.O (B₁.prod B₂).A a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := by
    rw [← _root_.GlobalTheory.RhoProd.rho_prod K B₁ B₂]
    exact congrArg _ hA'
  rw [hr, Nat.cast_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.UnramifiedHomBound

noncomputable def homToH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    U →ₗ[O] NG.H1z (Representation.trivial O G M) :=
  (Submodule.mkQ _).comp (Submodule.inclusion
    (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h))

theorem homToH1_injective {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    Function.Injective (homToH1 U hU) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  apply Subtype.ext
  funext g
  have h := congrFun hv g
  have h2 : NG.coD0 (Representation.trivial O G M) v g = 0 := by simp [NG.coD0]
  exact h.symm.trans h2

theorem homToH1_mem_unrH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) (I : Subgroup G)
    (c : U) (hc : ∀ g ∈ I, (c : G → M) g = 0) :
    homToH1 U hU c ∈ RepresentationBoundsCohomology.BR.unrH1 (Representation.trivial O G M) I := by
  change NG.resH1 (Representation.trivial O G M) I (Submodule.Quotient.mk _) = 0
  rw [NG.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  have h : NG.restrictCocycles1 (Representation.trivial O G M) I (Submodule.inclusion
      (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h) c)
      = 0 := Subtype.ext (funext fun g => hc g g.2)
  rw [h]
  exact Submodule.zero_mem _

theorem l_ne_zero (D : D7) (i : D.nd.Loc) : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := by
  have : CharZero (FractionRing (D.nd.O i)) :=
    charZero_of_injective_ringHom (D.nd.embK i).injective
  intro h
  have h2 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
  rw [map_natCast, map_zero] at h2
  exact (Fact.out : (D.nd.l i).Prime).ne_zero (Nat.cast_eq_zero.1 h2)

theorem length_unrHom_le (h : ReciprocityTheory.ChartRestriction.T2.VhE) (D : D7) (i : D.nd.Loc) :
    Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) ≤
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) *
        (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hU : ∀ c ∈ TruncatedSeriesCountingIdentities.unrHom i, ∀ g h, c (g * h) = c g + c h := fun c hc => hc.2.1
  rw [(LinearEquiv.ofInjective _ (homToH1_injective _ hU)).length_eq]
  refine h D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2 (D.nd.l i) (D.nd.O i)
    (Or.inr (IsTotallyComplex.nrRealPlaces_eq_zero _)) (KmodO (D.nd.O i))
    ⟨Submodule.quotEquivOfEq _ _ (Submodule.one_eq_range).symm⟩ _ (fun _ _ => rfl) _ ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl, c.2.1⟩
  · rintro v _ ⟨c, rfl⟩
    exact homToH1_mem_unrH1 _ hU _ c (c.2.2.2 v)

theorem unramified_homs_bounded_by_class_number_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  intro hA D i
  have h := length_unrHom_le (GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA) D i
  have hfin : Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) ≠ ⊤ :=
    Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (l_ne_zero D i)))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hfin
  have hlt : Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    rw [← he, ← Nat.cast_mul]
    exact ENat.natCast_lt_top _
  refine ⟨hlt, ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
  rw [← he, ← hn, ← Nat.cast_mul, Nat.cast_le] at h
  unfold lenUnit
  rw [← he, ← hn, ENat.toNat_natCast, ENat.toNat_natCast]
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  rw [mul_comm]
  exact_mod_cast h

end GlobalTheory.UnramifiedHomBound
end

