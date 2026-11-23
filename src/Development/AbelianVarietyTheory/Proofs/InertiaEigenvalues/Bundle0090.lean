module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicator
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.FourUnit

theorem integral_indicator_char_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (S : Set G) (φ : G → ℂ)
    (hφ : ∀ a b, φ (a + b) = φ a * φ b) (t : G) (hS : ∀ z, t + z ∈ S ↔ z ∈ S) (ht : φ t ≠ 1) :
    ∫ z, S.indicator φ z ∂μ = 0 := by
  have key : ∀ z, S.indicator φ (t + z) = φ t * S.indicator φ z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem ((hS z).2 hz), Set.indicator_of_mem hz, hφ]
    · rw [Set.indicator_of_notMem (fun h => hz ((hS z).1 h)), Set.indicator_of_notMem hz, mul_zero]
  have h := integral_add_left_eq_self (μ := μ) (S.indicator φ) t
  simp_rw [key, integral_const_mul] at h
  have h2 : (φ t - 1) * ∫ z, S.indicator φ z ∂μ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) ht
  · exact h3

theorem addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem norm_trace_le (hU : Unram F E) (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) (w : E) :
    ‖Algebra.trace F E w‖ ≤ ‖w‖ := by
  haveI := hU.ultraE
  rw [← norm_algebraMap' E, htr]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hU.norm_star]; simp)

theorem integral_ball_char (hU : Unram F E) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (hu : ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) (y : E) :
    ∫ z, (Metric.closedBall (0 : E) 1).indicator (fun z => ψ (Algebra.trace F E (star z * y))) z ∂μ =
      if ‖y‖ ≤ 1 then 1 else 0 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  split_ifs with hy
  · rw [Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun z hz => ?_)]
    · rw [integral_indicator measurableSet_closedBall, setIntegral_const]
      simp [Measure.real, hvol]
    · apply hψ.1
      refine (norm_trace_le hU htr _).trans ?_
      rw [norm_mul, hU.norm_star]
      exact mul_le_one₀ (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hy
  · push_neg at hy
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    obtain ⟨yF, hyF⟩ := hU.unram y
    obtain ⟨u, hu1, hu2⟩ := hu
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hyF0 : yF ≠ 0 := by rintro rfl; rw [hyF] at hy; simp at hy; linarith
    have hx₀y : ‖x₀‖ ≤ ‖y‖ := by
      have h1 : ‖yF⁻¹‖ < 1 := by rw [norm_inv, ← hyF]; exact inv_lt_one_of_one_lt₀ hy
      have h2 := hx₀' _ h1
      rw [norm_mul, norm_inv, ← hyF] at h2
      have hpos : 0 < ‖y‖ := by linarith
      rwa [mul_inv_le_iff₀ hpos, one_mul] at h2
    have htu : Algebra.trace F E u ≠ 0 := by intro h; rw [h, norm_zero] at hu2; exact zero_ne_one hu2
    set w : E := (x₀ / Algebra.trace F E u) • u with hw
    have hTw : Algebra.trace F E w = x₀ := by
      rw [hw, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ htu]
    have hnw : ‖w‖ ≤ ‖y‖ := by
      rw [hw, norm_smul, norm_div, hu2, div_one]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans hx₀y
    have hpos : 0 < ‖y‖ := by linarith
    refine integral_indicator_char_eq_zero μ _ _ (fun a b => ?_) (star (w * y⁻¹)) (fun z => ?_) ?_
    · rw [star_add, add_mul, map_add (f := _), AddChar.map_add_eq_mul]
    · have ht : ‖star (w * y⁻¹)‖ ≤ 1 := by
        rw [hU.norm_star, norm_mul, norm_inv, mul_inv_le_iff₀ hpos, one_mul]; exact hnw
      simp only [mem_closedBall_zero_iff]
      constructor
      · intro h
        have := IsUltrametricDist.norm_add_le_max (star (w * y⁻¹) + z) (-(star (w * y⁻¹)))
        rw [norm_neg, show star (w * y⁻¹) + z + -star (w * y⁻¹) = z by abel] at this
        exact this.trans (max_le h ht)
      · intro h
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht h)
    · simp only [star_star]
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one, hTw]
      exact hx₀

theorem fourU_unitU : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
    (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ htr hu
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  funext X
  simp only [fourU]
  by_cases h0 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1
  · have hint : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) =
        ∏ i, (Metric.closedBall (0 : E) 1).indicator
          (fun z => ψ (Algebra.trace F E (star z * X.2.1 i))) (c i) := by
      intro c
      by_cases hc : ∀ i, ‖c i‖ ≤ 1
      · have e1 : unitU r F E (X.1, c, X.2.2) = 1 := by
          simp only [unitU]; rw [Set.indicator_of_mem (by exact ⟨h0.1, hc, h0.2⟩)]; rfl
        rw [e1, one_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, Pi.star_apply, map_sum, addChar_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hc i))]
      · push_neg at hc
        obtain ⟨i, hi⟩ := hc
        have e1 : unitU r F E (X.1, c, X.2.2) = 0 := by
          simp only [unitU]
          apply Set.indicator_of_notMem
          intro h
          exact (not_le.2 hi) (h.2.1 i)
        rw [e1, zero_mul]
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (mem_closedBall_zero_iff.1 h)) _
    simp_rw [hint]
    rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_ball_char hU M.μE M.volE ψ hψ htr hu]
    rw [Finset.prod_boole]
    simp only [unitU, Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_univ, true_implies, Pi.one_apply]
    simp [h0.1, h0.2]
  · have e : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) = 0 := fun c => by
      simp only [unitU]
      apply Set.indicator_of_notMem
      intro h
      exact h0 ⟨h.1, h.2.2⟩
    simp_rw [e, zero_mul, integral_zero]

end GlobalTheory.JR.FourUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerpEqPerpNb
section
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_nb {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ nb cK J L v ↔ ∃ m ∈ perp cK J L v, ∃ a : O, x = m + a • v := by
  unfold nb
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨m, hm, a, rfl⟩
  · rintro ⟨m, hm, a, rfl⟩
    exact ⟨m, hm, a • v, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, rfl⟩

theorem conj_mem_range (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {y : K}
    (hy : y ∈ (algebraMap O K).range) : cK y ∈ (algebraMap O K).range := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨c a, (hcK a).symm⟩

theorem nb_int (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hvv : hf cK J v v ∈ (algebraMap O K).range) {x y : Fin r → K}
    (hx : x ∈ nb cK J L v) (hy : y ∈ nb cK J L v) :
    hf cK J x y ∈ (algebraMap O K).range := by
  obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hx
  obtain ⟨m', hm', a', rfl⟩ := mem_nb.1 hy
  rw [mem_perp] at hm hm'
  have h1 : hf cK J m m' ∈ (algebraMap O K).range := (hSD m).1 hm.1 m' hm'.1
  have h2 : hf cK J m v ∈ (algebraMap O K).range := by
    rw [hf_conj cK hc2 J hJ]; exact conj_mem_range c cK hcK hm.2
  rw [hf_add_left, hf_add_right, hf_add_right, hf_algSmul_right, hf_algSmul_left,
    hf_algSmul_left, hf_algSmul_right, hcK]
  refine add_mem (add_mem h1 (mul_mem ⟨_, rfl⟩ h2)) (add_mem (mul_mem ⟨_, rfl⟩ hm'.2) ?_)
  exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : IsSD cK J (nb cK J L v) := by
  obtain ⟨hv, hw, hvv⟩ := hstep
  intro x
  refine ⟨fun hx y hy => nb_int c cK hcK hc2 hJ hϖ hSD hvv hx hy, fun hx => ?_⟩
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  have hperp_nb : ∀ m ∈ perp cK J L v, m ∈ nb cK J L v := fun m hm =>
    mem_nb.2 ⟨m, hm, 0, by simp⟩
  have hl0p : ϖ • l0 ∈ perp cK J L v := by
    refine mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩
    rw [hf_algSmul_right]; exact hβ'
  have hxl0 : algebraMap O K ϖ * hf cK J x l0 ∈ (algebraMap O K).range := by
    have := hx _ (hperp_nb _ hl0p)
    rwa [hf_algSmul_right] at this
  obtain ⟨e, he⟩ := exists_ratio hϖ hβ hβ' hxl0
  set b := c.symm e with hb
  have hcb : cK (algebraMap O K b) = algebraMap O K e := by rw [hcK, hb, RingEquiv.apply_symm_apply]
  set x' := x - b • v with hx'
  have hx'l0 : hf cK J x' l0 = 0 := by
    rw [hx', hf_sub_left, hf_algSmul_left, hcb, he, sub_self]
  have hx'm : ∀ m ∈ perp cK J L v, hf cK J x' m ∈ (algebraMap O K).range := by
    intro m hm
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx m (hperp_nb m hm)) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) (mem_perp.1 hm).2)
  have hx'L : x' ∈ L := by
    refine (hSD x').2 fun l hl => ?_
    obtain ⟨a, ha⟩ := exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw hl)
    have hm : l - a • l0 ∈ perp cK J L v := by
      refine mem_perp.2 ⟨L.sub_mem hl (L.smul_mem a hl0), ?_⟩
      rw [hf_sub_right, hf_algSmul_right, ha, sub_self]
      exact zero_mem _
    have : l = (l - a • l0) + a • l0 := by abel
    rw [this, hf_add_right, hf_algSmul_right, hx'l0, mul_zero, add_zero]
    exact hx'm _ hm
  have hx'p : x' ∈ perp cK J L v := by
    refine mem_perp.2 ⟨hx'L, ?_⟩
    rw [hf_conj cK hc2 J hJ]
    apply conj_mem_range c cK hcK
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx v hvnb) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) hvv)
  exact mem_nb.2 ⟨x', hx'p, b, by rw [hx']; abel⟩

theorem perp_eq_perp_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) {l0 : Fin r → K} (hl0 : l0 ∈ L)
    (hβ : hf cK J v l0 ∉ (algebraMap O K).range) :
    perp cK J L v = perp cK J (nb cK J L v) l0 := by
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  ext x
  constructor
  · intro hx
    refine mem_perp.2 ⟨mem_nb.2 ⟨x, hx, 0, by simp⟩, (hSD l0).1 hl0 x (mem_perp.1 hx).1⟩
  · intro hx
    obtain ⟨hxn, hxl⟩ := mem_perp.1 hx
    obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hxn
    have hm' := mem_perp.1 hm
    have h1 : algebraMap O K a * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [hf_add_right, hf_algSmul_right] at hxl
      have := sub_mem hxl ((hSD l0).1 hl0 m hm'.1)
      simpa using this
    have hγ : hf cK J l0 v ∉ (algebraMap O K).range := by
      intro h
      apply hβ
      rw [hf_conj cK hc2 J hJ l0 v]
      exact conj_mem_range c cK hcK h
    have hγ' : algebraMap O K ϖ * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [← hf_algSmul_right]; exact (hSD l0).1 hl0 _ hw
    obtain ⟨e, rfl⟩ := (ratio_mem_iff hϖ hγ hγ' a).1 h1
    refine mem_perp.2 ⟨?_, (hSDn v).1 hvnb _ hxn⟩
    rw [mul_comm ϖ e, mul_smul]
    exact L.add_mem hm'.1 (L.smul_mem e hw)

theorem good_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : Good cK J ϖ N (nb cK J L v) := by
  obtain ⟨hSD, habs, hidx⟩ := hL
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hQ : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := Nat.card_pos.ne'
  have hpL : perp cK J L v ≤ L := fun x hx => (mem_perp.1 hx).1
  have hpn : perp cK J L v ≤ nb cK J L v := fun x hx => mem_nb.2 ⟨x, hx, 0, by simp⟩
  have i1 := perp_relIndex c cK hcK hϖ hSD hv hw
  have hl0n : l0 ∉ nb cK J L v := by
    intro h
    have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
    exact hβ ((hSDn v).1 hvnb l0 h)
  have hwl0 : ϖ • l0 ∈ nb cK J L v := by
    refine hpn (mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩)
    rw [hf_algSmul_right]; exact hβ'
  have i2 := perp_relIndex c cK hcK hϖ hSDn hl0n hwl0
  rw [← perp_eq_perp_nb c cK hcK hc2 hJ hϖ hSD ⟨hv, hw, hvv⟩ hl0 hβ] at i2
  refine ⟨hSDn, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := habs x
    refine ⟨k + 1, hpn (mem_perp.2 ⟨?_, ?_⟩)⟩
    · rw [pow_succ', mul_smul]; exact L.smul_mem ϖ hk
    · rw [pow_succ', mul_smul, hf_algSmul_right]
      exact mul_pair_mem c cK hcK hϖ hSD hw hk
  · rw [← idx_eq_of_le hϖ hpn (by rw [i2]; exact hQ), idx_eq_of_le hϖ hpL (by rw [i1]; exact hQ),
      hidx]

end GlobalTheory.HermNbr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdOfVanishingAtPerfectValuationPoints
section
open scoped NNReal

namespace GlobalTheory

theorem perfectRing_valuationSubring_of_isAlgClosed (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by
  haveI : ExpChar V l := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective V l ?_
  intro v
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v : L) (Nat.pos_of_ne_zero hl0)
  have hyV : y ∈ V := by
    rw [← V.valuation_le_one_iff]
    have hv : V.valuation (v : L) ≤ 1 := (V.valuation_le_one_iff _).2 v.2
    rw [← hy, map_pow] at hv
    exact (pow_le_one_iff_of_nonneg (zero_le') hl0).1 hv
  refine ⟨⟨y, hyV⟩, ?_⟩
  apply Subtype.ext
  simp [frobenius_def, hy]

theorem s_points_kpt : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  intro l _ R _ u x hl hu hrad H M
  rcases _root_.GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd R u x M hu hrad with h | ⟨L, _, _, V, f, hfu, hfnu, hdvd⟩
  · exact h
  exfalso
  haveI : CharP V l := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f, hl, map_zero])
  haveI : PerfectRing V l := perfectRing_valuationSubring_of_isAlgClosed l V
  obtain ⟨hdom, hpre, hne, hnu, hcomp⟩ := _root_.GlobalTheory.adicCompletion_valuationRing_props V (f u) hfu hfnu
  obtain ⟨hl', hbij⟩ := _root_.GlobalTheory.PerfectCompletion.perfect l V (f u)
  set O := AdicCompletion (Ideal.span {f u}) V
  haveI : IsDomain O := hdom
  haveI : ValuationRing O := { toPreValuationRing := hpre }
  haveI : CharP O l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl'
  haveI : PerfectRing O l := ⟨hbij⟩
  let g : R →+* O := (algebraMap V O).comp f
  have hgx : g x = 0 := H O g hne hnu hcomp
  have hd : g x ∣ g u ^ M := by
    simpa [g, map_pow] using map_dvd (algebraMap V O) hdvd
  rw [hgx, zero_dvd_iff] at hd
  exact hne (by_contra fun h => pow_ne_zero M h hd)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
section
open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]

def ptrB (M : Meas r F E) (ψ : AddChar F ℂ) (f : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b, f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1) ∂(Measure.pi fun _ : Fin r => M.μF)

def rowMap (g : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) : Gl r F :=
  (Y.1, fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 0, Y.2.2.2)

def rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (Y : Gl r F) : ℂ := h (rowMap g Y)

def weil (M : Meas r F E) (ψ : AddChar F ℂ) (g : SpecialLinearGroup (Fin 2) F) (f : Gl r F → ℂ) : Gl r F → ℂ :=
  ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct g (ptrB M ψ f))))

def negB (f : Gl r F → ℂ) (Y : Gl r F) : ℂ := f (Y.1, -Y.2.1, Y.2.2.1, Y.2.2.2)

end GlobalTheory.JR.WeilMix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatSpanBasis
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.SgnBasis

theorem eta_mul_isUnit (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]

private theorem eta_det_trace_matrix_eq_of_span_eq (K : UQ) (B : InvAlg K)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A)
    (m : Fin (Module.finrank K.E B.A) → B.A)
    (hm : Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) :
    K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  classical
  have hP0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • e j = m l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [← hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hQ0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • m j = e l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose P hP using hP0
  choose Q hQ using hQ0

  have hli : LinearIndependent K.O e :=
    e.linearIndependent.restrict_scalars fun a b h =>
      IsFractionRing.injective K.O K.E (by simpa [Algebra.smul_def] using h)

  have hsum : ∀ l, ∑ i, (∑ j, Q l j * P j i) • e i = e l := by
    intro l
    calc ∑ i, (∑ j, Q l j * P j i) • e i = ∑ j, Q l j • ∑ i, P j i • e i := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = e l := by simp only [hP, hQ]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext l i
    have key : ∑ i, ((Matrix.of Q * Matrix.of P) l i - (1 : Matrix _ _ K.O) l i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, hsum, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ key i)
  have hunit : IsUnit (Matrix.of P).det := Matrix.isUnit_det_of_left_inverse hQP

  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) *
        (Matrix.of P).transpose.map (algebraMap K.O K.E) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hP l]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, mul_smul_comm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K.E (P l j), map_smul, smul_eq_mul, mul_comm]
  have hdet : ((Matrix.of P).transpose.map (algebraMap K.O K.E)).det =
      algebraMap K.O K.E (Matrix.of P).det := by
    rw [RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [hmat, Matrix.det_mul, hdet]
  exact eta_mul_isUnit K _ _ hunit

theorem sgnLat_span_basis (K : UQ) (B : InvAlg K) (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    B.sgnLat (Submodule.span K.O (Set.range e)) =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  dsimp only [InvAlg.sgnLat]
  exact eta_det_trace_matrix_eq_of_span_eq K B e _
    (Classical.epsilon_spec (p := fun m : Fin (Module.finrank K.E B.A) → B.A =>
      Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) ⟨e, rfl⟩)

end GlobalTheory.UnitLemma.SgnBasis
end

