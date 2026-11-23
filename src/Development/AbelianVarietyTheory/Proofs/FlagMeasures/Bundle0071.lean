module

public import Mathlib
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KtypesWithinSteps
section
open Formalism.REAL
open scoped InnerProductSpace

namespace GlobalTheory.KTypeSteps

theorem sqrt_nsq_eq {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_root {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  have h : ∀ c, root a b c * root a b c =
      (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      simp [root, hab]
    · by_cases h2 : c = b
      · subst h2
        simp [root, h1]
      · simp [root, h1, h2]
  simp only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem kSpan_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hne : μ ≠ ν) :
    kSpan ε E y ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  intro z hz
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply]
  exact kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x
    (mem_compact_span_self_general x) z hz

theorem pfil_one_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hfd : FiniteDimensional ℂ (kSpan ε E y))
    (hne : μ ≠ ν) (hne' : ∀ a b, ε a ≠ ε b → μ ≠ ν + root a b) :
    pfil ε E y 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  refine le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)
  · obtain ⟨hA, hθ⟩ := (arrModule V n ε E 1).1 hg
    have hKU := (arrModule V n ε E 1).2 hu
    have := noncompact_arr_finite_dimensional (j := 1) hfd
    obtain ⟨m, F, lam, hF, -, hsup⟩ := kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1)
      inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable
    change (arrV0 ε E y 1).map (thetaA E 1) ≤ _
    rw [← hsup, Submodule.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    obtain ⟨hmem, h0, hhi⟩ := hF i
    obtain ⟨a, b, hab, hlam⟩ := hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0
    have hθhi : KHighest ε E (lam i) (thetaA E 1 (F i)) := by
      refine ⟨fun c => ?_, fun c d hcd he => ?_⟩
      · rw [← hθ, hhi.1 c, map_smul]
      · rw [← hθ, hhi.2 c d hcd he, map_zero]
    have hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1) := by
      refine compact_span_le_of_stable ?_ (mem_compact_span_self_general _)
      intro c d hcd G hG
      rw [Submodule.mem_comap] at hG ⊢
      rw [hθ]
      exact compact_span_stable_general _ c d hcd _ hG
    exact hle.trans (Submodule.comap_mono
      (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))
  · rw [(pfilFacts V n ε E y hg).1]
    exact kSpan_le_ker hg hu hx hy hne

theorem ew_mem_pfil {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    {w : List (Fin n × Fin n)} (hw : w.length ≤ j) (hp : ∀ p ∈ w, ε p.1 ≠ ε p.2) {y : V}
    (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j :=
  Submodule.subset_span ⟨w, hw, hp, y, hy, rfl⟩

theorem ktypes_within_steps :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E →
      KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
      ∀ (j : ℕ) (μ : Fin n → ℝ), ∀ x ∈ pfil ε E u j, x ≠ 0 → KHighest ε E μ x →
        Real.sqrt (nsq (μ - Λ)) ≤ Real.sqrt 2 * j := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd j
  obtain ⟨h0, -, hst, -, -, -, hfin⟩ := pfilFacts V n ε E u hg
  induction j with
  | zero =>
    intro μ x hx hx0 hhi
    rw [h0] at hx
    have := compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0
    subst this
    simp [nsq, dot]
  | succ j ih =>
    intro μ x hx hx0 hhi
    by_contra hlt
    rw [not_le] at hlt
    push_cast at hlt
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have := hfin hfd j
    obtain ⟨m, y, lam, hy, -, hsup⟩ := kDecomp V n ε E (pfil ε E u j) inferInstance
      (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)
    have hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      intro i
      obtain ⟨hmem, hy0, hyh⟩ := hy i
      have hb := ih (lam i) (y i) hmem hy0 hyh
      refine pfil_one_le_ker hg hu hhi hyh
        (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_
      · intro h
        rw [h] at hlt
        nlinarith
      · intro a b hab h
        have hab' : a ≠ b := fun h => hab (h ▸ rfl)
        have ht := sqrt_nsq_add_le (lam i - Λ) (root a b)
        rw [nsq_root hab'] at ht
        have he : μ - Λ = lam i - Λ + root a b := by rw [h]; abel
        rw [he] at hlt
        nlinarith
    have hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      rw [← hsup]
      refine iSup_le fun i => le_trans ?_ (hone i)
      obtain ⟨g0, g1, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0]
      exact g1 0
    have hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b) := by
      intro a b
      rw [← hsup]
      refine iSup_le fun i z hz => hone i ?_
      obtain ⟨g0, -, -, g3, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0] at hz
      exact g3 0 a b z hz
    have hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hp, z, hz, rfl⟩
      cases w with
      | nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)
      | cons p w =>
        have hw' : w.length ≤ j := by simpa using hw
        exact hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)
    have := hC hx
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at this
    exact hx0 (inner_self_eq_zero.mp this)

end GlobalTheory.KTypeSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LatticeGens

section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

theorem exists_gens_of_between (A : Submodule R V) (m : R) (hm : m ≠ 0) (t : Finset V) :
    (∀ x ∈ t, m • x ∈ A) → ∀ L : Submodule R V, A ≤ L → L ≤ A ⊔ Submodule.span R (t : Set V) →
      ∃ t' : Finset V, t'.card ≤ t.card ∧ L = A ⊔ Submodule.span R (t' : Set V) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ L h1 h2
    exact ⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩
  | insert x t hx ih =>
    intro ht L h1 h2
    obtain ⟨t', hc, ht'⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right
    set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hI
    set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hJ
    have hIJ : I ≤ J := Submodule.comap_mono (sup_le_sup_right h1 _)
    have hI0 : I ≠ 0 := by
      intro h
      have : m ∈ I := Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))
      rw [h] at this
      exact hm (by simpa using this)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
    have haJ : a ∈ J := by
      rw [← ha]; exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 haJ
    have hls' : l + s = a • x := hls
    refine ⟨insert l t', ?_, le_antisymm ?_ ?_⟩
    · rw [Finset.card_insert_of_notMem hx]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro y hy
      have hy2 := h2 hy
      rw [Finset.coe_insert, Submodule.span_insert] at hy2
      obtain ⟨a0, ha0, z, hz, rfl⟩ := Submodule.mem_sup.1 hy2
      obtain ⟨w, hw, s0, hs0, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hr : r ∈ J := by
        have : r • x = ((a0 + (r • x + s0)) - a0) - s0 := by abel
        change r • x ∈ L ⊔ Submodule.span R (t : Set V)
        rw [this]
        exact sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)
      rw [← ha] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      have hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V) := hi
      have key : a0 + ((i + k * a) • x + s0) - k • l ∈
          L ⊓ (A ⊔ Submodule.span R (t : Set V)) := by
        refine ⟨sub_mem hy (L.smul_mem _ hl), ?_⟩
        have : a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s := by
          rw [add_smul, mul_smul, ← hls', smul_add]; abel
        rw [this]
        exact add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi')
          (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))
      rw [ht'] at key
      have hle : A ⊔ Submodule.span R (t' : Set V) ≤
          A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      simpa using add_mem (hle key) hl'
    · rw [Finset.coe_insert, Submodule.span_insert]
      refine sup_le h1 (sup_le ?_ ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).2 hl
      · exact (le_sup_right.trans ht'.ge).trans inf_le_left

end Dedekind

section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem idxN_smul_mem (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx

theorem card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by
  have h := AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom
  have hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup := by
    ext x; simp
  rw [hk] at h
  unfold idxN
  rw [h]
  rfl

theorem encard_between_le (A B : Submodule R V) (hn : idxN B A ≠ 0) (e : ℕ)
    (h : ∀ L, A ≤ L → L ≤ B →
      ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span R (t' : Set V)) :
    {L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞) := by
  have hfin : Finite (B.map A.mkQ) := Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])
  let Φ : (Fin e → B.map A.mkQ) → Submodule R V := fun f =>
    (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ
  have hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ := by
    rintro L ⟨h1, h2⟩
    obtain ⟨t, hc, ht⟩ := h L h1 h2
    obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hc)
    let g : Fin e → V := Function.extend emb (fun x => (x : V)) 0
    have hg : ∀ i, g i ∈ Submodule.span R (t : Set V) := by
      intro i
      by_cases hi : ∃ x, emb x = i
      · obtain ⟨x, rfl⟩ := hi
        simp only [g, emb.injective.extend_apply]
        exact Submodule.subset_span x.2
      · simp only [g, Function.extend_apply' _ _ _ hi]
        simp
    have hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨i, rfl⟩; exact hg i
      · intro x hx
        exact ⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩
    have hgB : ∀ i, g i ∈ B := fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))
    refine ⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩
    have : (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g := by
      rw [← Set.range_comp]; rfl
    change (Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L
    rw [this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]
  calc {L | A ≤ L ∧ L ≤ B}.encard ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin e → B.map A.mkQ)).encard := Set.encard_image_le _ _
    _ = _ := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]
      simp

end Count

theorem exists_scaled_span (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)

theorem gens_and_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  intro K V _ _ _ _ _ _ _ A B hAB hn
  have hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨fun hB => ?_, fun e t hc ht => ?_⟩
  · obtain ⟨c, t, hc0, hcard, hcB, hBt⟩ := exists_scaled_span K V B hB
    obtain ⟨t', h1, h2⟩ := exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c)
      (mul_ne_zero hn' hc0) t
      (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB
      (hBt.trans le_sup_right)
    exact ⟨t', h1.trans hcard, h2⟩
  · have key : ∀ L, A ≤ L → L ≤ B →
        ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
      intro L h1 h2
      obtain ⟨t', h3, h4⟩ := exists_gens_of_between A _ hn' t
        (fun x hx => idxN_smul_mem A B
          (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1
        (h2.trans ht.le)
      exact ⟨t', h3.trans hc, h4⟩
    exact ⟨encard_between_le A B hn e key, key⟩

end GlobalTheory.Mass.LatticeGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosets
section
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

theorem inv_encard_stab_ne {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) (y : G ⧸ K0) :
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ 0 ∧
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ ⊤ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆
        {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0} := by
      intro γ hγ
      simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
      refine ⟨hγ.1, ?_⟩
      have h2 := hγ.2
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
      have := K0.inv_mem h2
      simpa [mul_assoc] using this
    have hfin := (hF g).subset hsub
    have hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty :=
      ⟨1, Subgroup.one_mem _⟩
    constructor
    · rw [ne_eq, ENNReal.inv_eq_zero]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤ := by
        exact_mod_cast h
      exact (Set.encard_ne_top_iff.2 hfin) this
    · rw [ne_eq, ENNReal.inv_eq_top]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0 := by
        exact_mod_cast h
      exact hne.ne_empty (Set.encard_eq_zero.1 this)

theorem mass_quotient_pos_finite {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) :
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ 0 ∧
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ ⊤ := by
  obtain ⟨S, hS⟩ := hS
  have hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0)) := by
    let f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0) := fun a =>
      Quotient.mk _ ((a.1 : G) : G ⧸ K0)
    refine Finite.of_surjective f ?_
    intro o
    induction o using Quotient.inductionOn with
    | h y =>
      induction y using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Quotient.sound
        refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
        show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _
        rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa [mul_assoc] using K0.inv_mem hκ
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))
  constructor
  · rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    exact ⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)

theorem mass_orbit_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0 hS hF
  obtain ⟨V, hV⟩ := GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0 := MulAction.stabilizer_quotient K0
  have h0 := hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
    (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
  have horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩
  simp only [horb, ite_true, hstab] at h0
  rw [show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one,
    mul_one] at h0
  obtain ⟨hV0, hVt⟩ := mass_quotient_pos_finite Γ K0 hS hF
  have hV0' : V ≠ 0 := by rw [← h0]; exact hV0
  have hVt' : V ≠ ⊤ := by rw [← h0]; exact hVt
  refine ⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩
  rw [hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']

end GlobalTheory.HL
end

