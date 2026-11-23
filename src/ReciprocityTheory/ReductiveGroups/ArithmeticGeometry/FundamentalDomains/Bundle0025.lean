module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
  ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem m3bExp_holds : FourierJacobiExpansion (E := E) := by
  classical
  intro r X la P hP ξ hξ x hx s hs
  obtain ⟨hξΛ, hξ0, -⟩ := id hξ

  obtain ⟨n, ω, hω⟩ : ∃ (n : ℕ) (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)),
      Submodule.span ℤ (Set.range ω) = perL X la := by
    let b := (Module.Free.chooseBasis ℤ (perL X la)).reindex (Fintype.equivFin _)
    exact ⟨_, b.ofZLatticeBasis ℝ (perL X la), b.ofZLatticeBasis_span ℝ (perL X la)⟩
  have hωp : ∀ j, ω j ∈ X.periods la := by
    intro j
    have h1 : ω j ∈ perL X la := by
      rw [← hω]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact h1

  have hsurj : ∀ u : X.Ψ → ℂ, ∃ t : Fin n → ℂ, TubeSummability.Lc X ω t = u := by
    intro u
    refine ⟨fun j => (ω.repr (fun τ => (u τ).re) j : ℂ) +
      (ω.repr (fun τ => (u τ).im) j : ℂ) * I, ?_⟩
    funext τ
    have hre : ∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ = (u τ).re := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).re)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    have him : ∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ = (u τ).im := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).im)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    simp only [TubeSummability.Lc]
    calc _ = ((∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ : ℝ) : ℂ) +
          ((∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ : ℝ) : ℂ) * I := by
          push_cast
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = u τ := by
          rw [hre, him]
          exact Complex.re_add_im (u τ)
  obtain ⟨t, rfl⟩ := hsurj s
  have ht : t ∈ tube n (TubeSummability.Om X ξ x ω) :=
    (TubeSummability.flow_Lc_mem_dom (ω := ω) hξ0 hx t).mp hs
  have hΩ := TubeSummability.Om_open_convex (ξ := ξ) (ω := ω) hx
  have hexp : HasSum (fun k : Fin n → ℤ =>
      fourCoeff (TubeSummability.hline X P ξ x ω) 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * t j))
      (P (X.flow ξ (TubeSummability.Lc X ω t) x)) :=
    (TubeFourierExpansion.tube_expansion (TubeSummability.Om X ξ x ω) (TubeSummability.hline X P ξ x ω) hΩ.1 hΩ.2
      (TubeSummability.zero_mem_Om (ω := ω) hξ0 hx) (TubeSummability.hline_diff (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω) hP hξ0 hx)
      (TubeSummability.hline_periodic (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω)
        hP hξΛ hξ0 hx hωp) t ht).2
  refine ((FrequencyIndexing.νk_injective (ω := ω)).hasSum_iff ?_).mp ?_
  · intro ν hν
    have hfj : X.fj la ξ ν P x = 0 := by
      rw [Data.fj]
      refine if_neg ?_
      intro hall
      apply hν
      choose k hk using fun j => hall (ω j) (hωp j)
      exact ⟨k, (FrequencyIndexing.eq_νk (ω := ω) ν k hk).symm⟩
    simp only [hfj, zero_mul]
  · convert hexp using 1
    funext k
    simp only [Function.comp_apply]
    congr 1
    · exact FlowMeanContinuity.fj_eq_fourCoeff (X := X) (la := la) P hP hξ hx ω hω
        (FrequencyIndexing.νk ω k) k (FrequencyIndexing.νk_spec (ω := ω) k)
    · congr 1
      have key : ∀ j, ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * (ω j τ : ℂ) = (k j : ℂ) / 2 := by
        intro j
        have h2 := FrequencyIndexing.νk_spec (ω := ω) k j
        have h3 : ∑ τ, FrequencyIndexing.νk ω k τ * ω j τ = (k j : ℝ) / 2 := by linarith
        exact_mod_cast h3
      have hsw : ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * TubeSummability.Lc X ω t τ =
          ∑ j, t j * ((k j : ℂ) / 2) := by
        simp only [TubeSummability.Lc, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← key j, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun τ _ => by ring)
      rw [hsw, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModelNefness
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Matrix NumberField Complex Module

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem reductionTheory_holds : MahlerCompactnessCriterion (E := E) := by
  unfold MahlerCompactnessCriterion
  intro r X ε hε
  classical
  have hm : (0:ℝ) < ε ^ 2 := by positivity
  have hB0 : (0:ℝ) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) := by positivity
  set B : ℝ := 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) with hB_def
  have hC : 0 ≤ HermitianPsiBounds.Cinv X := HermitianPsiBounds.Cinv_nonneg (X := X)
  have hD : (0:ℝ) ≤ ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set D : ℝ := ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ with hD_def
  have hR : 0 ≤ D * ((B + B) * HermitianPsiBounds.Cinv X) := mul_nonneg hD (mul_nonneg (add_nonneg hB0 hB0) hC)
  set R : ℝ := D * ((B + B) * HermitianPsiBounds.Cinv X) with hR_def
  have hW : (0:ℝ) ≤ ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set W : ℝ := ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 with hW_def
  set T : ℝ := 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 with hT_def
  have hfin := FiniteTranslateSets.TS_finite (X := X) (ι := Fin (finrank ℤ X.Λ)) R T hR

  obtain ⟨rep, hrep⟩ : ∃ rep : _ → Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      ∀ t ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T, HermitianLatticeMaps.ty X (rep t) = t := by
    refine ⟨fun t => if h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t
      then h.choose else RealPlaceEmbeddings.zb X, fun t ht => ?_⟩
    have h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t := by
      simp only [FiniteTranslateSets.TS, Set.mem_setOf_eq] at ht
      obtain ⟨f, -, hf⟩ := ht
      exact ⟨f, hf⟩
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨S, hS⟩ := X.Γ_index
  let q := fun t (s : GL (Fin r) E) (k : Fin r) (i : Fin (finrank ℤ X.Λ)) =>
    (RealPlaceEmbeddings.qb X (rep t)).repr ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i
  have hQ : (0:ℝ) ≤ ∑ t ∈ hfin.toFinset, ∑ s ∈ S, ∑ k : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
      ‖((q t s k i : ℚ) : ℂ)‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  set Q : ℝ := ∑ t ∈ hfin.toFinset, ∑ s ∈ S, ∑ k : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
      ‖((q t s k i : ℚ) : ℂ)‖ with hQ_def
  have hG0 : (0:ℝ) ≤ ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  set G0 : ℝ := ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ with hG0_def
  refine ⟨CompactEntryBounds.Kset X (∑ _k : Fin r, G0 * (Q * (1 + B * HermitianPsiBounds.Cinv X))),
    CompactEntryBounds.Kset_compact (X := X) _, CompactEntryBounds.Kset_sub (X := X) _, ?_⟩
  intro x hx hl
  obtain ⟨b, hb, hnf⟩ := MajorantNormalForms.exists_normal_frame (X := X) hx
  have hy : IntegralBasisReduction.IsNormal X (mat (rmul x b)) := by
    unfold IntegralBasisReduction.IsNormal
    intro τ
    exact ⟨CompactEntryBounds.det_ne_of_gram (X := X) (hnf τ).1, (hnf τ).1⟩
  have hmin : ∀ v ∈ X.Λ, v ≠ 0 → ε ^ 2 ≤ QuadraticLatticeForms.Qy X (mat (rmul x b)) v := fun v hv hv0 =>
    HermitianPsiBounds.sq_le_Qy_of_le_firstMinimum (X := X) (x := x) (y := mat (rmul x b)) (fun τ u => (hnf τ).2 u) hε hl hv hv0
  obtain ⟨f, hfB, hfZ⟩ := IntegralBasisReduction.reduce (X := X) hy hm hmin

  have hmem : HermitianLatticeMaps.ty X f ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T := by
    simp only [FiniteTranslateSets.TS, FiniteTranslateSets.Sh, FiniteTranslateSets.Sz, Set.mem_setOf_eq]
    refine ⟨f, ⟨fun i j => ?_, fun k i j => ?_⟩, rfl⟩
    · refine ⟨⟨(X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
        X.Λ_int _ (f i).2 _ (f j).2⟩, rfl, fun σ => ?_⟩
      show ‖σ ((X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E))‖ ≤ R
      rw [map_mul, norm_mul]
      have h1 : ‖σ (X.den : E)‖ ≤ D :=
        Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      have h2 := HermitianPsiBounds.herm_bound (X := X) hy σ (f i : Fin r → E) (f j : Fin r → E)
      have h3 : (QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) +
          QuadraticLatticeForms.Qy X (mat (rmul x b)) (f j : Fin r → E)) * HermitianPsiBounds.Cinv X ≤
          (B + B) * HermitianPsiBounds.Cinv X :=
        mul_le_mul_of_nonneg_right (add_le_add (hfB i) (hfB j)) hC
      exact mul_le_mul h1 (h2.trans h3) (norm_nonneg _) hD
    · show (((f.repr (RingOfIntegers.basis E k • f i) j : ℤ) : ℝ)) ^ 2 ≤ T
      have h2 : QuadraticLatticeForms.Qy X (mat (rmul x b))
          ((RingOfIntegers.basis E k • f i : X.Λ) : Fin r → E) ≤ W * B := by
        rw [HermitianLatticeMaps.smul_coe (X := X)]
        refine (HermitianPsiBounds.Qy_smul (X := X) _ _ _).trans
          (mul_le_mul ?_ (hfB i) (QuadraticLatticeForms.Qy_nonneg (X := X) _ _) hW)
        exact Finset.single_le_sum (f := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
            ∑ τ : X.Ψ, ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      calc _ ≤ _ := hfZ _ j
        _ ≤ 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 := by gcongr
  have hts : HermitianLatticeMaps.ty X (rep (HermitianLatticeMaps.ty X f)) = HermitianLatticeMaps.ty X f := hrep _ hmem
  obtain ⟨γ, hγU, -, hγinv⟩ :=
    HermitianLatticeMaps.exists_gl (X := X) (f := f) (f' := rep (HermitianLatticeMaps.ty X f)) hts.symm
  obtain ⟨s, hsS, hsΓ⟩ := hS γ hγU
  refine ⟨s⁻¹ * γ, hsΓ, b, hb, ?_⟩
  have hgU := X.Γ_stab _ hsΓ
  simp only [CompactEntryBounds.Kset, Set.mem_setOf_eq]
  intro τ
  have hgram : gram τ.1 X.Gm (((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat (rmul x b) τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
    rw [CompactEntryBounds.gram_stab (X := X) hgU.1]
    exact (hnf τ).1
  refine ⟨hgram, fun a c => ?_⟩
  show ‖(((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    mat (rmul x b) τ) a c‖ ≤ _
  have hdet := CompactEntryBounds.det_ne_of_gram (X := X) hgram
  refine (CompactEntryBounds.entry_bound (X := X) hdet hgram a c).trans (Finset.sum_le_sum fun k _ => ?_)
  refine mul_le_mul ?_ ?_ (norm_nonneg _) hG0
  · have e1 := Finset.single_le_sum (f := fun a' : Fin r => ‖(X.Gm.map τ.1)⁻¹ k a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have e2 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ a' : Fin r, ‖(X.Gm.map τ.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have e3 := Finset.single_le_sum
      (f := fun τ' : X.Ψ => ∑ k' : Fin r, ∑ a' : Fin r, ‖(X.Gm.map τ'.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ τ)
    exact e1.trans (e2.trans e3)
  · have hemb : Data.emb τ.1 (Pi.single k (1:E)) = Pi.single k 1 := by
      funext a'
      by_cases h : a' = k
      · subst h; simp [Data.emb]
      · simp [Data.emb, h]
    have hcol : ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹) c k =
        ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single k 1)) c := by
      rw [hemb]
      first
        | (simp; done)
        | (simp [Matrix.mulVec, dotProduct, Pi.single_apply]; done)
        | (simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]; done)
    rw [hcol, CompactEntryBounds.inv_lact]
    have hginv : (((s⁻¹ * γ)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1 =
        ∑ i, q (HermitianLatticeMaps.ty X f) s k i • (f i : Fin r → E) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hγinv _
    rw [hginv]
    refine (CompactEntryBounds.comb_bound (X := X) (mat (rmul x b)) τ (q (HermitianLatticeMaps.ty X f) s k)
      (fun i => (f i : Fin r → E)) c).trans ?_
    have hterm : ∀ i, ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ *
        (1 + QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) / X.c τ) ≤
        ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ * (1 + B * HermitianPsiBounds.Cinv X) := by
      intro i
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (norm_nonneg _)
      rw [div_eq_mul_one_div]
      exact mul_le_mul (hfB i) (HermitianPsiBounds.inv_c_le (X := X) τ)
        (le_of_lt (one_div_pos.mpr (QuadraticLatticeForms.c_pos (X := X) τ))) hB0
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg zero_le_one (mul_nonneg hB0 hC))
    have i1 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ i : Fin (finrank ℤ X.Λ), ‖((q (HermitianLatticeMaps.ty X f) s k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have i2 := Finset.single_le_sum
      (f := fun s' : GL (Fin r) E => ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q (HermitianLatticeMaps.ty X f) s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hsS
    have i3 := Finset.single_le_sum
      (f := fun t' => ∑ s' ∈ S, ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q t' s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (hfin.mem_toFinset.mpr hmem)
    exact i1.trans (i2.trans i3)

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosDefOfBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

lemma dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)

lemma quad_AtA {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]

lemma posDef_of_bound {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    change x i ≠ 0 at hi
    have : 0 < ‖x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

