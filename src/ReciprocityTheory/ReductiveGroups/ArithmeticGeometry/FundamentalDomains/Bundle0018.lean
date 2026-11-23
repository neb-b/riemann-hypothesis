module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowIsotropicPairs
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma herm_swap_eq_zero_of_eq_zero (X : Data E r) (x y : Fin r → E) (h : herm X.Gm x y = 0) :
    herm X.Gm y x = 0 := by
  have e : cc (herm X.Gm x y) = herm X.Gm y x := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    first
      | (have hg := X.Gm_herm b a
         simp only [cc] at hg
         rw [hg]
         ring)
      | (have hg := X.Gm_herm a b
         simp only [cc] at hg
         rw [hg]
         ring)
  rw [← e, h]
  simp [cc]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_smul_right_eq_cc_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem isIsoPair_of (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hxξ : herm X.Gm x ξ = 0)
    (hxx : herm X.Gm x x = 0) (hne : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
  obtain ⟨-, hξξ, hξ0⟩ := hξ
  have hξx : herm X.Gm ξ x = 0 := herm_swap_eq_zero_of_eq_zero X.toData x ξ hxξ
  unfold IsIsoPair
  refine ⟨?_, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  · intro i k
    fin_cases i <;> fin_cases k <;>
      simp [herm_smul_left_fundamental_domains, herm_smul_right_eq_cc_mul, hξξ, hxξ, hxx, hξx]
  · by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNC : (X.NC : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NC_pos.ne'
      have htn : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNC
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]
        exact eq_neg_of_add_eq_zero_right hst
      apply hne (-(s / (t * X.NC)))
      calc x = (t * X.NC)⁻¹ • ((t * X.NC) • x) := by rw [smul_smul, inv_mul_cancel₀ htn, one_smul]
        _ = -(s / (t * X.NC)) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem mem_pair (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hx : x ∈ X.L') :
    ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
  obtain ⟨hξΛ, -, -⟩ := hξ
  intro i
  fin_cases i
  · exact hξΛ
  · exact X.NC_sub x hx

theorem xp_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) = 0 ∧
      X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
  set α := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hα
  have hxp : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x - α • Data.emb τ.1 ξ := rfl
  have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hxξ, map_zero]
  have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb, hξξ, map_zero]
  have h3 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 x) = 0 := by
    rw [hermC_emb, hxx, map_zero]
  have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
  have hne : X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz0 τ]
    exact_mod_cast (X.maj_pos hz0 τ (emb_ne_zero τ.1 hξ0)).ne'
  rw [hxp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hermC_sub_left, hermC_smul_left, h1, h2, mul_zero, sub_zero]
  · simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
    simp
  · rw [Hf_sub_left, Hf_smul_left, hα, div_mul_cancel₀ _ hne, sub_self]

theorem e_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (e : X.Ψ → Fin r → ℂ) (hxp0 : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0)
    (he : ∀ τ, e τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
      X.ucomp z0 ξ (X.embV x) τ) :
    X.IsIsoV e ∧ (∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0) ∧
      (∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) ∧ (∀ τ, X.c τ * X.maj z0 τ (e τ) = 1) := by
  have key : ∀ τ, ∃ k : ℝ, 0 < k ∧ e τ = (k : ℂ) • X.ucomp z0 ξ (X.embV x) τ ∧
      k ^ 2 * (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    have hm : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
      mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hz0 τ (hxp0 τ))
    refine ⟨(Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹,
      inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_, ?_⟩
    · simp only [he τ, Complex.ofReal_inv]
    · rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨k, hk, hek, -⟩ := key τ
    have hf := xp_facts X hξξ hξ0 hxξ hxx hz0 τ
    refine ⟨?_, ?_⟩
    · rw [hek, hermC_smul_left, hermC_smul_right, hf.2.1, mul_zero, mul_zero]
    · rw [hek]
      exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne') (hxp0 τ)
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, hermC_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).1, mul_zero]
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, Hf_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).2.2, mul_zero]
  · obtain ⟨k, -, hek, hk2⟩ := key τ
    rw [hek, maj_smul X hz0, ← hk2]
    ring

theorem flow_facts (X : Data E r) {ξ : Fin r → E} {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.FramesOverBasis ξ)
    (e : X.Ψ → Fin r → ℂ) (hiso : X.IsIsoV e)
    (heξ : ∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0)
    (hHe : ∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) (hce : ∀ τ, X.c τ * X.maj z0 τ (e τ) = 1)
    {z : Frame X.Ψ r} (hz : z ∈ X.dom) (hf : X.SameFlag z0 z) :
    (∀ τ, X.ttV e z τ = 1) ∧ X.flowV e (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ := by
  have httv : ∀ τ, X.ttV e z τ = 1 := by
    intro τ
    rw [Data.ttV, maj_flag X hz0.1 hz hf, hce τ, div_one]
  have hTz : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := by
    refine (flowDomainCriterion_holds r X e hiso z hz (fun _ => -(I / 2))).1.mpr fun τ => ?_
    rw [httv τ]
    norm_num
  refine ⟨httv, hTz, fun τ => ?_⟩
  have hve : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (e τ) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, heξ τ, map_zero]
  have hpe : hermC τ.1 X.Gm (X.ppos z τ (Data.emb τ.1 ξ)) (e τ) = 0 :=
    hpe_of X hz τ (Data.emb τ.1 ξ) (e τ) (by rw [Hf_flag X hz0.1 hz hf]; exact hHe τ) (heξ τ)
  rw [maj_flowV X e _ hz hTz τ _ hve hpe, maj_flag X hz0.1 hz hf, hz0.2 τ]

end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLineOfCovering
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem isotropic_outside_line_of_covering (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem isotropic_outside_line : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeMinorExistence
section
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_minor {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) :
    ∃ a b : Fin r, u 0 a * u 1 b - u 0 b * u 1 a ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu0 : u 0 ≠ 0 := hu.ne_zero 0
  obtain ⟨a, ha⟩ : ∃ a, u 0 a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (funext h)
  have key := Fintype.linearIndependent_iff.1 hu ![u 1 a, -(u 0 a)] (by
    funext b
    have hb := hcon a b
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply]
    linear_combination -hb)
  exact ha (by simpa using key 1)

lemma emb_li {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) (τ : E →+* ℂ) (c : Fin 2 → ℂ)
    (hc : ∑ i, c i • Data.emb τ (u i) = 0) : c = 0 := by
  obtain ⟨a, b, hab⟩ := exists_minor hu
  have hd : τ (u 0 a * u 1 b - u 0 b * u 1 a) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact hab
  simp only [map_sub, map_mul] at hd
  have ea := congrFun hc a
  have eb := congrFun hc b
  simp only [Finset.sum_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Data.emb,
    Pi.zero_apply] at ea eb
  have h0 : c 0 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 1 b) * ea - τ (u 1 a) * eb
  have h1 : c 1 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 0 a) * eb - τ (u 0 b) * ea
  have h0' := (mul_eq_zero.1 h0).resolve_right hd
  have h1' := (mul_eq_zero.1 h1).resolve_right hd
  funext i
  fin_cases i
  · simpa using h0'
  · simpa using h1'

variable (X : Data E r)

lemma uvec_ne {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) {a : X.Ψ → Fin 2 → ℂ} {τ : X.Ψ}
    (ha : a τ ≠ 0) : X.uvec u a τ ≠ 0 := fun h0 => ha (emb_li hu τ.1 (a τ) h0)

lemma hermC_uvec {u : Fin 2 → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (a b : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) = 0 := by
  have key : hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) =
      ∑ i, ∑ k, a τ i * conj (b τ k) * τ.1 (herm X.Gm (u i) (u k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, herm, Data.uvec, Data.emb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_sum, map_mul, emb_cc, Fin.sum_univ_two, map_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  simp [hu]

lemma isIsoV_uvec {u : Fin 2 → Fin r → E} (hu : IsIsoPair X.Gm u) {a : X.Ψ → Fin 2 → ℂ}
    (ha : ∀ τ, a τ ≠ 0) : X.IsIsoV (X.uvec u a) := fun τ => ⟨hermC_uvec X hu.1 a a τ, uvec_ne X hu.2 (ha τ)⟩

lemma herm_rank1 (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    IsHermFam (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) := by
  intro τ i k
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma pairR_rank1 (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) = ∑ τ, s τ * (X.chiAt χ a τ).re := by
  unfold Data.pairR Data.chiAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma posSemidef_of {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) (τ0 : X.Ψ)
    (h : ∀ x : Fin 2 → ℂ, x ≠ 0 → 0 ≤ (∑ i, ∑ k, χ τ0 i k * conj (x i) * x k).re) :
    (Matrix.of (χ τ0)).PosSemidef := by
  have hH : (Matrix.of (χ τ0)).IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hχ τ0 k i]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have hre : (star x ⬝ᵥ (Matrix.of (χ τ0)).mulVec x) =
      ∑ i, ∑ k, χ τ0 i k * conj (x i) * x k := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [hre, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · exact h x hx
  · rw [← hre]
    exact him.symm

lemma chiAt_embH (β : Matrix (Fin 2) (Fin 2) E) (c : Fin 2 → E) (τ : X.Ψ) :
    X.chiAt (X.embH β) (fun σ i => σ.1 (c i)) τ = τ.1 (∑ i, ∑ k, β i k * c i * cc (c k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Data.chiAt, Data.embH, map_sum, map_mul, emb_cc]

lemma herm_of_LZ {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  intro τ i k
  simp only [Data.embH]
  rw [← hβ i k, emb_cc]

lemma herm_comb {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, IsHermFam (ω j))
    (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]

end

end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
end

