module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.PAdicHodge.PerfectoidField

@[expose] public section

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsCover
section
namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {i : ℕ}
    (L : Submodule (RingOfIntegers K) (Fin i → K))
    (hL : Submodule.span K (L : Set (Fin i → K)) = ⊤) (v : Fin i → K) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  let T : Submodule K (Fin i → K) :=
    { carrier := {v | ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨d₁, h₁, ha⟩ ⟨d₂, h₂, hb⟩
        refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.smul_mem _ ha
        · rw [mul_smul]; exact L.smul_mem _ hb
      smul_mem' := by
        rintro c v ⟨d, hd, hv⟩
        obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
        refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
        have key : ((b : RingOfIntegers K) * d) • (c • v) = a • (d • v) := by
          rw [← algebraMap_smul K ((b : RingOfIntegers K) * d) (c • v), ← algebraMap_smul K a (d • v),
            ← algebraMap_smul K d v, smul_smul, smul_smul]
          congr 1
          simp only [map_mul] at hab ⊢
          rw [← hab]
          ring
        rw [key]
        exact L.smul_mem _ hv }
  have hT : Submodule.span K (L : Set (Fin i → K)) ≤ T :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [hL] at hT
  exact hT Submodule.mem_top

theorem exists_cover {K : Type} [Field K] [NumberField K] {i : ℕ}
    {F X : GroundTheory.Heights₂.Heights.HermLattice K i} :
    X.lattice < F.lattice →
      ∃ w ∈ F.lattice,
        w ∉ X.lattice ∧
          ∀ (N : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
            X.lattice ≤ N →
              N ≤ X.lattice ⊔ NumberField.RingOfIntegers K ∙ w →
                N = X.lattice ∨ N = X.lattice ⊔ NumberField.RingOfIntegers K ∙ w := by
  classical
  intro hXF
  obtain ⟨s, hs⟩ := F.fg

  obtain ⟨d, hd0, hdX⟩ : ∃ d : RingOfIntegers K, d ≠ 0 ∧ ∀ f ∈ F.lattice, d • f ∈ X.lattice := by
    choose e he hem using fun v => exists_ne_zero_smul_mem X.lattice X.span_eq v
    refine ⟨∏ g ∈ s, e g, Finset.prod_ne_zero_iff.2 fun g _ => he g, fun f hf => ?_⟩
    rw [← hs] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase s e (Finset.mem_coe.1 hx), mul_comm, mul_smul]
      exact X.lattice.smul_mem _ (hem x)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact X.lattice.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact X.lattice.smul_mem a hx
  have : Finite (RingOfIntegers K ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])

  let rep := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {d}))
  let P : (s → RingOfIntegers K ⧸ Ideal.span {d}) → (Fin i → K) :=
    fun q => ∑ a : s, rep (q a) • (a : Fin i → K)
  have key : ∀ v ∈ F.lattice, ∃ q, v - P q ∈ X.lattice := by
    intro v hv
    rw [← hs, Submodule.mem_span_finset'] at hv
    obtain ⟨c, rfl⟩ := hv
    refine ⟨fun a => Ideal.Quotient.mk _ (c a), ?_⟩
    have ht : ∀ a, ∃ t, t * d = c a - rep (Ideal.Quotient.mk _ (c a)) := fun a =>
      Ideal.mem_span_singleton'.1
        (Ideal.Quotient.eq.1 (Function.surjInv_eq (Ideal.Quotient.mk_surjective) _).symm)
    choose t ht using ht
    have hsum : ∑ a : s, c a • (a : Fin i → K) - P (fun a => Ideal.Quotient.mk _ (c a)) =
        d • ∑ a : s, t a • (a : Fin i → K) := by
      simp only [P]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sub_smul, ← ht a, mul_comm, mul_smul]
    rw [hsum]
    apply hdX
    rw [← hs]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span a.2)

  let S : Set (Submodule (RingOfIntegers K) (Fin i → K)) :=
    {N | X.lattice < N ∧ N ≤ F.lattice}
  let g : Submodule (RingOfIntegers K) (Fin i → K) → Set (s → RingOfIntegers K ⧸ Ideal.span {d}) :=
    fun N => {q | P q ∈ N}
  have sub : ∀ N₁ N₂ : Submodule (RingOfIntegers K) (Fin i → K), X.lattice ≤ N₁ →
      N₁ ≤ F.lattice → X.lattice ≤ N₂ → g N₁ ⊆ g N₂ → N₁ ≤ N₂ := by
    intro N₁ N₂ h₁ hF h₂ hg v hv
    obtain ⟨q, hq⟩ := key v (hF hv)
    have hPq : P q ∈ N₁ := by
      have := N₁.sub_mem hv (h₁ hq)
      rwa [sub_sub_cancel] at this
    have hPq₂ : P q ∈ N₂ := hg hPq
    have := N₂.add_mem (h₂ hq) hPq₂
    rwa [sub_add_cancel] at this
  have hinj : Set.InjOn g S := by
    intro N₁ h₁ N₂ h₂ h
    exact le_antisymm (sub N₁ N₂ h₁.1.le h₁.2 h₂.1.le h.subset)
      (sub N₂ N₁ h₂.1.le h₂.2 h₁.1.le h.symm.subset)
  have hfin : S.Finite := Set.Finite.of_finite_image (Set.toFinite (g '' S)) hinj
  obtain ⟨N, hN⟩ := hfin.exists_minimal ⟨F.lattice, hXF, le_rfl⟩
  obtain ⟨w, hwN, hwX⟩ := SetLike.exists_of_lt hN.1.1
  refine ⟨w, hN.1.2 hwN, hwX, fun N' h1 h2 => ?_⟩
  have hle : X.lattice ⊔ RingOfIntegers K ∙ w ≤ N :=
    sup_le hN.1.1.le ((Submodule.span_singleton_le_iff_mem _ _).2 hwN)
  by_cases h : N' = X.lattice
  · exact Or.inl h
  · right
    have hlt : X.lattice < N' := lt_of_le_of_ne h1 (Ne.symm h)
    have hNN' := hN.2 ⟨hlt, (h2.trans hle).trans hN.1.2⟩ (h2.trans hle)
    exact le_antisymm h2 (hle.trans hNN')

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.TiltCountableNeighbourhoods
section
namespace GroundTheory.Variant₂.N1

open GroundTheory.PAdicHodge

section

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

private lemma mem_integers_iff (x : K) : x ∈ (normInteger K) ↔ ‖x‖ ≤ 1 := by
  change NormedField.valuation x ≤ 1 ↔ _
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

private lemma norm_eq_of_norm_sub_lt {u z : K} (h : ‖u - z‖ < ‖z‖) : ‖u‖ = ‖z‖ := by
  have h1 : ‖u‖ ≤ max ‖u - z‖ ‖z‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (u - z) z
  have h2 : ‖z‖ ≤ max ‖z - u‖ ‖u‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (z - u) u
  rw [norm_sub_rev] at h2
  apply le_antisymm
  · exact h1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.mp h2 with h3 | h3
    · exact absurd h3 (not_le.mpr h)
    · exact h3

private lemma norm_le_of_mem_span {x : (normInteger K)} {p : ℕ}
    (hx : x ∈ Ideal.span {((p : (normInteger K)))}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hc : ‖(c : K)‖ ≤ 1 := (mem_integers_iff (c : K)).mp c.2
  simp only [Subring.coe_mul, Subring.coe_natCast, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : (normInteger K))] [IsAdicComplete (Ideal.span {(p : (normInteger K))}) (normInteger K)]

private lemma exists_untilt_norm_of_lt
    (hsurj : Function.Surjective fun x : ModP (normInteger K) p => x ^ p)
    {x : K} (hpx : ‖(p : K)‖ < ‖x‖) (hx1 : ‖x‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : (normInteger K)) : K)‖ = ‖x‖ := by
  let x' : (normInteger K) := ⟨x, (mem_integers_iff x).mpr hx1⟩
  let s : ℕ → ModP (normInteger K) p := fun n => Nat.rec (Ideal.Quotient.mk _ x')
    (fun _ t => Classical.choose (hsurj t)) n
  have hs : ∀ n, s (n + 1) ^ p = s n := fun n => Classical.choose_spec (hsurj (s n))
  let a : PreTilt (normInteger K) p := ⟨s, hs⟩
  refine ⟨a, ?_⟩
  have h0 : Ideal.Quotient.mk _ (PreTilt.untilt a) = Ideal.Quotient.mk (Ideal.span {(p : (normInteger K))}) x' := by
    rw [PreTilt.mk_untilt_eq_coeff_zero]
    rfl
  have hdiff : ‖((PreTilt.untilt a : (normInteger K)) : K) - x‖ ≤ ‖(p : K)‖ := by
    have hmem := Ideal.Quotient.eq.mp h0
    simpa [x'] using norm_le_of_mem_span hmem
  exact norm_eq_of_norm_sub_lt (lt_of_le_of_lt hdiff hpx)

private lemma exists_untilt_norm
    (hsurj : Function.Surjective fun x : ModP (normInteger K) p => x ^ p)
    {t : K} (hpt : ‖(p : K)‖ < ‖t‖) (ht1 : ‖t‖ < 1)
    {y : K} (hy : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : (normInteger K)) : K)‖ = ‖y‖ := by
  obtain ⟨at', hat⟩ := exists_untilt_norm_of_lt hsurj hpt ht1.le
  have ht0 : 0 < ‖t‖ := lt_of_le_of_lt (norm_nonneg _) hpt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hy) ht1

  induction n generalizing y with
  | zero =>
    exact absurd hy1 (not_le.mpr (by simpa using hn))
  | succ n ih =>
    by_cases hyt : ‖t‖ < ‖y‖
    · exact exists_untilt_norm_of_lt hsurj (hpt.trans hyt) hy1
    · rw [not_lt] at hyt
      have htne : t ≠ 0 := norm_pos_iff.mp ht0
      have hv : ‖y / t‖ = ‖y‖ / ‖t‖ := norm_div y t
      obtain ⟨b, hb⟩ := ih (y := y / t) (div_ne_zero hy htne)
        (by rw [hv]; exact (div_le_one ht0).mpr hyt)
        (by rw [hv, lt_div_iff₀ ht0, ← pow_succ]; exact hn)
      refine ⟨at' * b, ?_⟩
      rw [map_mul, Subring.coe_mul, norm_mul, hat, hb, hv, mul_div_cancel₀ _ ht0.ne']

end

theorem exists_norm_untilt_eq_norm_of_norm_le_one {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] {p : ℕ} [Fact (Nat.Prime p)] [IsPerfectoidField K p] {y : K}
    (hy : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : normInteger K) : K)‖ = ‖y‖ := by
  obtain ⟨t, hpt, ht1⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) p ‖(p : K)‖
    IsPerfectoidField.norm_natCast_lt_one
  exact exists_untilt_norm IsPerfectoidField.surjective_pow hpt ht1 hy hy1

end GroundTheory.Variant₂.N1
end

