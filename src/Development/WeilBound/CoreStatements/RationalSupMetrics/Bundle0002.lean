module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.RationalSupMetrics.ExistsFormWithValuation
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

private theorem isMultiHomog_mul_rational_sup_metrics {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {d e : K → ℕ} (hf : IsMultiHomog f d) (hg : IsMultiHomog g e) : IsMultiHomog (f * g) (d + e) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem MultiProjectiveCoordinates.exists_form_with_valuation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  intro K _ ι _ Ω _ y hbir hrel a s
  classical
  choose i hi using hrel
  have hev : ∀ f : MRing ι, eval (fun _ => (1 : Ω)) (mConeMap y f) = aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simp [mConeMap]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  have hy : ∀ k, y ⟨k, i k⟩ ≠ 0 := by
    intro k hk
    apply hi k
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, hk]
  let mon : (K → ℕ) → ((Σ k, ι k) →₀ ℕ) := fun e =>
    Finsupp.equivFunOnFinite.symm (fun p => if p = ⟨p.1, i p.1⟩ then e p.1 else 0)
  have hmon_homog : ∀ e, IsMultiHomog (monomial (mon e) (1 : ℤ) : MRing ι) e := by
    intro e m hm k
    have hm' := support_monomial_subset hm
    rw [Finset.mem_singleton] at hm'
    subst hm'
    simp [mon]
  have hmon_ne : ∀ e, aeval y (monomial (mon e) (1 : ℤ) : MRing ι) ≠ 0 := by
    intro e
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rw [Finsupp.mem_support_iff] at hp
    by_cases hpe : p = ⟨p.1, i p.1⟩
    · rw [hpe]
      exact hy _
    · exact absurd (by simp [mon, hpe]) hp
  obtain ⟨Mp, hMph, hMpn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (a k).toNat) 1, hmon_homog (fun k => (a k).toNat), hmon_ne (fun k => (a k).toNat)⟩
  obtain ⟨Mn, hMnh, hMnn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (-a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (-a k).toNat) 1, hmon_homog (fun k => (-a k).toNat), hmon_ne (fun k => (-a k).toNat)⟩
  clear hmon_homog hmon_ne
  obtain ⟨d, g0, h0, hg0, hh0, hy0, hgy0⟩ := hbir (s * aeval y Mn / aeval y Mp)
  have hH : IsMultiHomog (h0 * Mn) (d + fun k => (-a k).toNat) := isMultiHomog_mul_rational_sup_metrics hh0 hMnh
  have hG : IsMultiHomog (g0 * Mp) (d + fun k => (a k).toNat) := isMultiHomog_mul_rational_sup_metrics hg0 hMph
  refine ⟨h0 * Mn, ⟨⟨_, hH⟩, ?_⟩, ?_⟩
  · intro hmem
    have hk : mConeMap y (h0 * Mn) = 0 := RingHom.mem_ker.mp hmem
    have hz := congrArg (eval fun _ => (1 : Ω)) hk
    rw [hev, map_zero, map_mul] at hz
    exact mul_ne_zero hy0 hMnn hz
  · intro 𝕜 _ z hz
    refine ⟨aeval z (g0 * Mp) / aeval z (h0 * Mn), _, _, g0 * Mp, h0 * Mn, hG, hH, ?_, ?_, hz, ?_⟩
    · intro k
      simp only [Pi.add_apply]
      push_cast
      omega
    · rw [map_mul, map_mul, hgy0]
      field_simp
    · rw [div_mul_cancel₀ _ hz]
end

-- bundled from Development.WeilBound.CoreStatements.RationalSupMetrics.HermitianLineShiftProperties
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.levi_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((shiftH A t).h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
  have h1 : (fun z => Real.log ((shiftH A t).h z)) =ᶠ[𝓝 z] fun z => t + Real.log (A.h z) := by
    filter_upwards [MultiProjectiveCoordinates.isOpen_blocks.mem_nhds hz] with z' hz'
    show Real.log (Real.exp t * A.h z') = _
    rw [Real.log_mul (Real.exp_pos t).ne' (A.pos z' hz').ne', Real.log_exp]
  have h2 : fderiv ℝ (fun z => t + Real.log (A.h z)) = fderiv ℝ (fun z => Real.log (A.h z)) :=
    funext fun z => fderiv_const_add t
  unfold leviForm
  rw [h1.fderiv.fderiv_eq, h2]

theorem MultiProjectiveCoordinates.shiftH_smooth_nef_gen : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  intro K _ ι _ P A t Λ
  have hs : IsSmoothHerm A → IsSmoothHerm (shiftH A t) := fun h => contDiffOn_const.mul h
  have hp : (∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P A) →
      ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P (shiftH A t) := by
    rintro ⟨P0, h0, h1, h2⟩
    refine ⟨P0, h0, hs h1, fun z hz w hw => ?_⟩
    rw [MultiProjectiveCoordinates.levi_shift A t hz.1]
    exact h2 z hz w hw
  have hc : IsConjInvariantH A → IsConjInvariantH (shiftH A t) := fun h z => by
    show Real.exp t * _ = Real.exp t * _
    rw [h z]
  refine ⟨hs, fun h => ⟨hp h.semipos, hc h.conj, h.nef⟩, fun h =>
    ⟨mul_pos h.pos (Real.exp_pos _), hp h.semipos, hc h.conj, ?_⟩⟩
  obtain ⟨a, ha, hm⟩ := h.mono
  refine ⟨a, ha, fun z hz μ hμ => (hm z hz μ hμ).trans_eq ?_⟩
  show Λ * A.h z = Λ * Real.exp (-t) * (Real.exp t * A.h z)
  rw [mul_assoc, ← mul_assoc (Real.exp (-t)), ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
end

-- bundled from Development.WeilBound.CoreStatements.RationalSupMetrics.ValuationUniqueOnForms
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.valuation_unique_on_forms : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  intro K _ ι _ Ω _ y 𝕜 _ a s z w hz hw
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩ := hw
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h := by
    intro dg dh g h hg hh hd e
    have hdeg : dg0 + dh = dg + dh0 := by
      funext k
      have h1 := hd k
      have h2 := hd0 k
      simp only [Pi.add_apply]
      omega
    have f1 := MultiProjectiveCoordinates.Val.mh_mul hg hh0
    have f2 := MultiProjectiveCoordinates.Val.mh_mul hg0 hh
    rw [hdeg] at f2
    have h3 := MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by
      rw [map_sub, map_mul, map_mul, e, e0]
      ring)
    rw [map_sub, map_mul, map_mul, e1] at h3
    apply mul_right_cancel₀ hne
    linear_combination h3
  refine ⟨key, ?_⟩
  rintro w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩
  have := key dg dh g h hg hh hd e
  exact mul_right_cancel₀ hn (e'.symm.trans this)
end

