module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0003
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SmoothContinuousAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0006
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CPtsat
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem ptsat_segre (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre]

theorem ptsat_cons (y : Fin e → ℂ) : star (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 (star y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem ptsat_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : star z ∈ mcPts P :=
  ((_root_.GlobalTheory.CompanionTheory.Ar.Cmp.conj_basic K ι).1 P z).2 hz

theorem ptsat_symm (h : ∀ w, Ψ' w = star (Ψ (star w))) (w) : Ψ w = star (Ψ' (star w)) := by
  rw [h, star_star, star_star]

theorem ptsat_fibre (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w} (hw : w ∈ fibre P Ψ' y) :
    star w ∈ fibre P Ψ (star y) := by
  obtain ⟨z, hz, rfl, h2⟩ := hw
  exact ⟨star z, ptsat_mem hz, ptsat_segre z, by rw [ptsat_symm h, star_star, h2, ptsat_cons]⟩

theorem ptsat_sheet (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w γ} (hγ : IsSheet P Ψ' y w γ) :
    IsSheet P Ψ (star y) (star w) (star ∘ γ ∘ star) := by
  refine ⟨by simp only [Function.comp_apply, star_star, ptsat_segre, hγ.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star y)) (𝓝 y) := by
    simpa using (continuous_star (R := Fin e → ℂ)).tendsto (star y)
  filter_upwards [ht.eventually hγ.2] with y' hy'
  refine ⟨by simpa using hy'.1.star_star, ptsat_mem hy'.2.1, ?_⟩
  rw [ptsat_symm h, Function.comp_apply, Function.comp_apply, ptsat_segre, star_star, hy'.2.2, ptsat_cons,
    star_star]

end

theorem c_ptsat : SheetIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w i, Ψ' w i = starRingEnd ℂ (Ψ (fun c => starRingEnd ℂ (w c)) i)) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  intro hS K _ ι _ P e Ψ Ψ' L A s hP hΨ h0 hL hA hs
  have h : ∀ w, Ψ' w = star (Ψ (star w)) := fun w => funext (h0 w)
  refine ⟨fun z hz h1 => hΨ _ (ptsat_mem hz) (by rw [ptsat_symm h, ptsat_segre, star_star, h1, star_zero]), ?_⟩
  have hm : MeasureTheory.MeasurePreserving (star : (Fin e → ℂ) → Fin e → ℂ) :=
    MeasureTheory.volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have he : MeasurableEmbedding (star : (Fin e → ℂ) → Fin e → ℂ) :=
    (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
  unfold ptsIntegralAt
  rw [← hm.integral_comp he (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hm.quasiMeasurePreserving.ae (hS K ι P e Ψ L A s hP hΨ hL hA hs)] with y hy
  refine finsum_mem_eq_of_bijOn star ⟨fun w hw => ptsat_fibre h hw, star_injective.injOn, fun w hw =>
    ⟨star w, by simpa using ptsat_fibre (ptsat_symm h) hw, star_star w⟩⟩ fun w _ => ?_
  unfold sheetDensity
  by_cases h1 : ∃ γ, IsSheet P Ψ' y w γ
  · have h2 : ∃ γ, IsSheet P Ψ (star y) (star w) γ := ⟨_, ptsat_sheet h h1.choose_spec⟩
    rw [dite_eq_left h1, dite_eq_left h2, hy _ _ _ h2.choose_spec (ptsat_sheet h h1.choose_spec),
      (_root_.GlobalTheory.CompanionTheory.Ar.Cmp.conj_basic K ι).2.2.2.1]
    have h3 := c_madens e (fun j y' => pot L j ((star ∘ h1.choose ∘ star) y')) y
    congr 1
    · simp only [Function.comp_apply, star_star]
      rfl
    · refine Eq.trans ?_ h3
      congr 1
      funext j y'
      show _ = pot L j (star (h1.choose (star (star y'))))
      rw [star_star]
      rfl
  · have h2 : ¬ ∃ γ, IsSheet P Ψ (star y) (star w) γ := fun ⟨γ, hγ⟩ =>
      h1 ⟨_, by simpa only [star_star] using ptsat_sheet (ptsat_symm h) hγ⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflag
section
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace PositivityTheory.UnitarySelfGeneration

private theorem l_genflag_lemma_0 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c'' c' c : Fin n → E) {A B : Matrix (Fin n) (Fin n) Ω} (hA : ∀ k, c'' k = ∑ l, A l k • c' l)
    (hB : ∀ k, c' k = ∑ l, B l k • c l) : ∀ k, c'' k = ∑ p, (B * A) p k • c p := by
  intro k
  rw [hA k]
  simp_rw [hB, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

private theorem l_genflag_lemma {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : ∀ k, c k ∈ Submodule.span Ω (Set.range c')) :
    ∃ h : Matrix (Fin n) (Fin n) Ω, ∀ k, c k = ∑ l, h l k • c' l := by
  choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hc k)
  exact ⟨Matrix.of fun l k => f k l, fun k => by simp only [Matrix.of_apply]; exact (hf k).symm⟩

private theorem l_genflag_lemma_2 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : LinearIndependent Ω c) {h P : Matrix (Fin n) (Fin n) Ω}
    (hh : ∀ k, c k = ∑ l, h l k • c' l) (hP : ∀ k, c' k = ∑ l, P l k • c l) : P * h = 1 := by
  have key := l_genflag_lemma_0 c c' c hh hP
  ext p k
  have := Fintype.linearIndependent_iff.1 hc (fun p => (P * h) p k - (1 : Matrix (Fin n) (Fin n) Ω) p k)
    (by simp [sub_smul, Finset.sum_sub_distrib, ← key k, Matrix.one_apply]) p
  exact sub_eq_zero.1 this

private theorem l_genflag_lemma_3 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ} (S : Set (Fin n → F)) :
    Submodule.span K ((fun v l => f (v l)) '' (Submodule.span F S : Set (Fin n → F))) =
      Submodule.span K ((fun v l => f (v l)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe]
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      convert (Submodule.span K ((fun v l => f (v l)) '' S)).zero_mem using 1
      ext i; simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      ext i; simp
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (f a) hx using 1
      ext i; simp
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

private theorem l_genflag_lemma_4 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ}
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (M.map f) t = GF.fl (M'.map f) t := by
  have key : ∀ N : Matrix (Fin n) (Fin n) F, GF.fl (N.map f) t =
      Submodule.span K ((fun v l => f (v l)) '' (GF.fl N t : Set (Fin n → F))) := by
    intro N
    simp only [GF.fl, flagStep]
    rw [l_genflag_lemma_3, Set.image_image]
    rfl
  rw [key, key, h]

private theorem l_genflag_lemma_5 {F : Type} [Field F] {n : ℕ} (N : Matrix (Fin n) (Fin n) F)
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (N * M) t = GF.fl (N * M') t := by
  have key : ∀ M : Matrix (Fin n) (Fin n) F, GF.fl (N * M) t = (GF.fl M t).map (Matrix.mulVecLin N) := by
    intro M
    simp only [GF.fl, flagStep, Submodule.map_span, Set.image_image]
    congr 2
  rw [key, key, h]

open GF in
theorem l_genflag : ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] (E E₁ E₂ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [AddCommGroup E₂] [Module Ω₂ E₂] (j₁ : E →+ E₁) (j₂ : E →+ E₂) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (b₁ : ∀ s, Fin (r s) → E₁) (b₂ : ∀ s, Fin (r s) → E₂) (d₁ d₂ : ℕ), IsGenericFlag (Ω' := Ω₁) j₁ V b₁ d₁ → IsGenericFlag (Ω' := Ω₂) j₂ V b₂ d₂ → ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃), i₁.comp (algebraMap Ω Ω₁) = i₂.comp (algebraMap Ω Ω₂) ∧ (∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * d₁ = n₂ * d₂ ∧ Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂) ∧ ∀ s (c : Fin (r s) → E) (m₁ : Matrix (Fin (r s)) (Fin (r s)) Ω₁) (m₂ : Matrix (Fin (r s)) (Fin (r s)) Ω₂), LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V s → (∀ k, b₁ s k = ∑ l, m₁ l k • j₁ (c l)) → (∀ k, b₂ s k = ∑ l, m₂ l k • j₂ (c l)) → ∀ i, flagStep Ω₃ (fun k l => i₁ (m₁ l k) : Fin (r s) → Fin (r s) → Ω₃) i = flagStep Ω₃ (fun k l => i₂ (m₂ l k) : Fin (r s) → Fin (r s) → Ω₃) i := by
  intro Ω Ω₁ Ω₂ _ _ _ _ _ E E₁ E₂ _ _ _ _ _ _ j₁ j₂ S _ r V b₁ b₂ d₁ d₂ hG1 hG2
  unfold IsGenericFlag at hG1 hG2
  obtain ⟨c1, u1, hc1, hj1, hjc1, -, hd1, hup1, hfl1, hai1, hdpos1, hrk1⟩ := hG1
  obtain ⟨c2, u2, hc2, hj2, hjc2, -, hd2, hup2, hfl2, hai2, hdpos2, hrk2⟩ := hG2
  have hU1 : ∀ σ, GF.Uni (u1 σ) := fun σ => ⟨hd1 σ, hup1 σ⟩
  have hU2 : ∀ σ, GF.Uni (u2 σ) := fun σ => ⟨hd2 σ, hup2 σ⟩
  rw [GF.adjoin_all u1 hU1] at hrk1
  rw [GF.adjoin_all u2 hU2] at hrk2
  have hfd1 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u1))) Ω₁ :=
    Module.finite_of_finrank_pos (by rw [hrk1]; exact hdpos1)
  have hfd2 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2))) Ω₂ :=
    Module.finite_of_finrank_pos (by rw [hrk2]; exact hdpos2)
  have hA : ∀ σ, ∃ A : Matrix (Fin (r σ)) (Fin (r σ)) Ω,
      (∀ k, c2 σ k = ∑ l, A l k • c1 σ l) ∧ A.det ≠ 0 := by
    intro σ
    obtain ⟨A, hA⟩ := l_genflag_lemma (c2 σ) (c1 σ)
      (fun k => by rw [(hc1 σ).2, ← (hc2 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨B, hB⟩ := l_genflag_lemma (c1 σ) (c2 σ)
      (fun k => by rw [(hc2 σ).2, ← (hc1 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨A, hA, fun h0 => ?_⟩
    have hBA := congrArg Matrix.det (l_genflag_lemma_2 (c2 σ) (c1 σ) (hc2 σ).1 hA hB)
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at hBA
    exact zero_ne_one hBA
  choose A hAc hAdet using hA
  obtain ⟨u2', hU2', hai2', hadj, hfl2'⟩ := GF.change u2 hU2 hai2 hfd2 A hAdet
  have hfd2' : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ := by
    rw [hadj]; exact hfd2
  have hrk2' : Module.finrank (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ = d₂ := by
    rw [hadj]; exact hrk2
  obtain ⟨Ω₃, hF3, i₁, i₂, hα, hq, n₁, n₂, hn, hdeg, hr1, hr2⟩ :=
    GF.compositum' (GF.ent u1) (GF.ent u2') hai1 hai2' hfd1 hfd2'
  have hU : ∀ σ, (u1 σ).map i₁ = (u2' σ).map i₂ := by
    intro σ
    ext l k
    simp only [Matrix.map_apply]
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hq ⟨σ, ⟨(l, k), hkl⟩⟩
    · rw [(hU1 σ).1 k, (hU2' σ).1 k, map_one, map_one]
    · rw [(hU1 σ).2 l k hlk, (hU2' σ).2 l k hlk, map_zero, map_zero]
  refine ⟨Ω₃, hF3, i₁, i₂, RingHom.ext hα, ⟨n₁, n₂, hn, ?_, hr1, hr2⟩, ?_⟩
  · rw [← hrk1, ← hrk2', hdeg]
  intro s c m₁ m₂ hc hspan hb1 hb2 i
  obtain ⟨h1, hh1⟩ := l_genflag_lemma c (c1 s)
    (fun k => by rw [(hc1 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨P1, hP1⟩ := l_genflag_lemma (c1 s) c
    (fun k => by rw [hspan, ← (hc1 s).2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hP2 : ∀ k, c2 s k = ∑ p, (P1 * A s) p k • c p := l_genflag_lemma_0 (c2 s) (c1 s) c (hAc s) hP1
  obtain ⟨h2, hh2⟩ := l_genflag_lemma c (c2 s)
    (fun k => by rw [(hc2 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  have e1 : P1 * h1 = 1 := l_genflag_lemma_2 c (c1 s) hc hh1 hP1
  have e2 : (P1 * A s) * h2 = 1 := l_genflag_lemma_2 c (c2 s) hc hh2 hP2
  have f1 := GF.fl_coord j₁ hj1 (hjc1 s) hh1 hb1 (hfl1 s i)
  have f2 := GF.fl_coord j₂ hj2 (hjc2 s) hh2 hb2 (hfl2 s i)
  have g1 : GF.fl m₁ i = GF.fl (P1.map (algebraMap Ω Ω₁) * u1 s) i := by
    have := l_genflag_lemma_5 (P1.map (algebraMap Ω Ω₁)) f1
    rwa [← mul_assoc, ← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  have g2 : GF.fl m₂ i = GF.fl ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s) i := by
    have := l_genflag_lemma_5 ((P1 * A s).map (algebraMap Ω Ω₂)) f2
    rwa [← mul_assoc, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  change GF.fl (m₁.map i₁) i = GF.fl (m₂.map i₂) i
  rw [l_genflag_lemma_4 i₁ g1, l_genflag_lemma_4 i₂ g2]
  have hPβ : (P1.map (algebraMap Ω Ω₁)).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂ := by
    ext l k
    exact hα (P1 l k)
  have L : (P1.map (algebraMap Ω Ω₁) * u1 s).map i₁ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (u2' s).map i₂ := by
    rw [Matrix.map_mul, hPβ, hU s]
  have R : ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s).map i₂ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (((A s).map (algebraMap Ω Ω₂) * u2 s).map i₂) := by
    simp only [Matrix.map_mul, mul_assoc]
  rw [L, R]
  exact l_genflag_lemma_5 _ (l_genflag_lemma_4 i₂ (hfl2' s i))

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.REnlarge
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_enlarge : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ L L' : LocPot X) (s s' : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), 0 ≤ C₅ → 0 ≤ C → t₀ ≤ Real.exp (-1) → (∀ y, logNormSec L s y ≤ 0) → bdry s ⊆ bdry s' → (∀ y, y ∉ bdry s' → rW L s y ≤ rW L' s' y) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → IsSingWeight A L' s' th ph C₅ ∧ IsRegFamily A Θ L' s' th ph phT C t₀ ∧ IsRegFamilyC2 A s' ph phT := by
  intro e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2
  have hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s := fun y hy h => hy (hsub h)
  have hpos : ∀ y, 0 < rW L s y := by
    intro y
    unfold rW
    have h1 := hL y
    have h2 := Real.exp_pos 1
    linarith
  obtain ⟨hpot, hsm, hpsh, hb⟩ := hS
  obtain ⟨h0, h1, hf⟩ := hR
  refine ⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩
  · intro j
    exact (hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)
  · intro x j y hy w
    exact hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w
  · intro y hy
    obtain ⟨hlo, hhi⟩ := hb y (hnb y hy)
    refine ⟨?_, hhi⟩
    have hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y) := Real.log_le_log (hpos y) (hrw y hy)
    nlinarith [mul_le_mul_of_nonneg_left hlog hC5]
  · intro t ht htt
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hf t ht htt
    have hte : t ≤ Real.exp (-1) := le_trans htt ht0
    have h1t : Real.exp 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      calc Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have hL1 : 1 ≤ Real.log (1 / t) := by
      have h := Real.log_le_log (Real.exp_pos 1) h1t
      rwa [Real.log_exp] at h
    have heps : 0 ≤ epsT C t := by
      unfold epsT
      exact div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)
    refine ⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩
    · intro y hy hle
      exact a6 y (hnb y hy) (le_trans (hrw y hy) hle)
    · intro y hy
      have h7 := a7 y (hnb y hy)
      nlinarith [mul_le_mul_of_nonneg_left (hrw y hy) heps]
  · intro j K hK hKc
    exact hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RHolmap
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open HolomorphicMinorCharts in
theorem r_holmap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e e' : ℕ) (X Y : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) (V : Y → Set Y) (mu : Y → Y → (Σ k, ι k) → ℂ), IsEmbedded A P U lam → (∀ y, IsOpen (V y) ∧ y ∈ V y) → (∀ y p, B.HoloOn (V y) fun y' => mu y y' p) → (∀ y, ∀ y' ∈ V y, mu y y' ∈ mcPts P) → (∀ y y', ∀ w ∈ V y ∩ V y', SameOrbit (mu y w) (mu y' w)) → ∃ π : Y → X, HoloMap B A π ∧ ∀ y, SameOrbit (lam (π y) (π y)) (mu y y) := by
  intro K _ ι _ P e e' X Y _ _ _ _ A B U lam V mu hE hV hm hmem hc
  choose π hπ using fun y => hE.surj (mu y y) (hmem y y (hV y).2)
  have hcl := isClosed_minors (U := U) (lam := lam) (V := V) (mu := mu) (fun x => ⟨hE.isOpen x, hE.mem_U x⟩)
    (fun x p => holo_continuousAt (hE.holo x p) (hE.mem_U x)) hE.compat hV
    (fun y p => holo_continuousAt (hm y p) (hV y).2) hc
  have hcont : ∀ y, ContinuousAt π y := fun y =>
    continuousAt_of_closed_rel hcl (fun y => minors_of_so (hπ y)) fun x hx =>
      hE.inj _ _ (so_trans (so_of_minors hx (hE.mem x x (hE.mem_U x)).1 (hmem y y (hV y).2).1) (so_symm (hπ y)))
  refine ⟨π, ⟨continuous_iff_continuousAt.mpr hcont, fun j k w hw => ?_⟩, hπ⟩
  set y := (B.chart j).symm w with hy
  have h := analyticAt_factor (A := A) (B := B) (U := U (π y)) (lam := lam (π y)) (V := V y) (mu := mu y) (π := π)
    (y := y) (hE.holo _) (hE.mem_U _) (hm y) (hV y).2 (hcont y) (hE.mem _ _ (hE.mem_U _)).1 (hE.immersion (π y))
    (by
      filter_upwards [(hV y).1.mem_nhds (hV y).2, hcont y ((hE.isOpen _).mem_nhds (hE.mem_U (π y)))] with w' h1 h2
      exact so_trans (hE.compat _ _ _ ⟨h2, hE.mem_U _⟩) (so_trans (hπ w') (hc _ _ _ ⟨(hV _).2, h1⟩)))
    j k ((B.chart j).map_target hw.1) hw.2
  rwa [hy, (B.chart j).right_inv hw.1] at h

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RPluri
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

private theorem continuousOn_levi_of_contDiffOn' {e : ℕ} (d : (Fin e → ℂ) → ℝ) (c : Fin e → ℂ) (r : ℝ) (w : Fin e → ℂ)
    (hd2 : ContDiffOn ℝ 2 d (Metric.ball c r)) :
    ContinuousOn (fun v => ReciprocityTheory.AnForm.levi d v w) (Metric.ball c r) := by
  have hc0 := ReciprocityTheory.AnForm.continuousOn_levi Metric.isOpen_ball hd2
  refine hc0.comp (f := fun v : Fin e → ℂ => (v, w)) ?_ ?_
  · exact (continuous_id.prodMk continuous_const).continuousOn
  · intro v hv
    exact Set.mk_mem_prod hv (Set.mem_univ w)

open HolomorphicMinorCharts ReciprocityTheory.AnForm in
theorem r_pluri : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X), IsPotential A P → IsPotential A Q → IsOpen U → Dense U → SamePot A U P Q → SamePot A Set.univ P Q := by
  intro e X _ _ _ A U P Q hP hQ hUo hUd hS x _
  obtain ⟨j, hxj⟩ := A.cover x
  set ψ := A.chart j with hψ
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) :=
    ψ.isOpen_inter_preimage_symm ((P.isOpen_U x).inter (Q.isOpen_U x))
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x) := by
    refine ⟨ψ.map_source hxj, ?_⟩
    show ψ.symm (ψ x) ∈ P.U x ∩ Q.U x
    rw [ψ.left_inv hxj]
    exact ⟨P.mem_U x, Q.mem_U x⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (ψ x) hxO
  set d : (Fin e → ℂ) → ℝ := fun z => P.φ x (ψ.symm z) - Q.φ x (ψ.symm z) with hdd
  have h1 := (hP.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.1⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' P.U x))
  have h2 := (hQ.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.2⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' Q.U x))
  have hd2 : ContDiffOn ℝ 2 d (Metric.ball (ψ x) r) :=
    ((h1.sub h2).mono hball).of_le (WithTop.coe_le_coe.mpr le_top)
  clear_value d
  clear h1 h2
  have hzero : ∀ z ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x), ψ.symm z ∈ U → ∀ w, levi d z w = 0 := by
    intro z hz hzU w
    have hyPx : ψ.symm z ∈ P.U x := hz.2.1
    have hyQx : ψ.symm z ∈ Q.U x := hz.2.2
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hEq1⟩ := hP.2 x (ψ.symm z) (ψ.symm z) ⟨hyPx, P.mem_U _⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hEq2⟩ := hQ.2 x (ψ.symm z) (ψ.symm z) ⟨hyQx, Q.mem_U _⟩
    obtain ⟨V3, hV3o, hyV3, G3, hG3, hEq3⟩ := hS (ψ.symm z) hzU
    have hNo : IsOpen (W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z)) :=
      ((((((hW1o.inter hW2o).inter hV3o).inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter
        (Q.isOpen_U x)).inter (Q.isOpen_U _))
    have hyN : ψ.symm z ∈ W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z) :=
      ⟨⟨⟨⟨⟨⟨hyW1, hyW2⟩, hyV3⟩, hyPx⟩, P.mem_U _⟩, hyQx⟩, Q.mem_U _⟩
    have hH : AnalyticAt ℂ (fun v => G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)) z :=
      ((hG1 j z ⟨hz.1, hyW1⟩).sub (hG2 j z ⟨hz.1, hyW2⟩)).add (hG3 j z ⟨hz.1, hyV3⟩)
    have hev : d =ᶠ[𝓝 z] fun v => (G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)).re := by
      have hmem := (ψ.continuousAt_symm hz.1).preimage_mem_nhds (hNo.mem_nhds hyN)
      filter_upwards [hmem] with v hv
      obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hv
      have e1 := hEq1 _ ⟨⟨a1, a4⟩, a5⟩
      have e2 := hEq2 _ ⟨⟨a2, a6⟩, a7⟩
      have e3 := hEq3 _ a3
      simp only [hdd, Complex.add_re, Complex.sub_re]
      linarith
    rw [levi_congr hev w]
    exact levi_re_analytic hH w
  have hlevi : ∀ z ∈ Metric.ball (ψ x) r, ∀ w, levi d z w = 0 := by
    intro z hz w
    by_contra hne
    have hcw := continuousOn_levi_of_contDiffOn' d (ψ x) r w hd2
    have hca : ContinuousAt (fun v => levi d v w) z := hcw.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hM : (fun v => levi d v w) ⁻¹' {b | b ≠ 0} ∩ Metric.ball (ψ x) r ∈ 𝓝 z :=
      Filter.inter_mem (hca.preimage_mem_nhds (isOpen_ne.mem_nhds hne)) (Metric.isOpen_ball.mem_nhds hz)
    obtain ⟨M, hMsub, hMo, hzM⟩ := mem_nhds_iff.mp hM
    have hzt : z ∈ ψ.target := (hball (hMsub hzM).2).1
    have hne2 : (ψ.source ∩ ψ ⁻¹' M).Nonempty := by
      refine ⟨ψ.symm z, ψ.map_target hzt, ?_⟩
      show ψ (ψ.symm z) ∈ M
      rw [ψ.right_inv hzt]
      exact hzM
    obtain ⟨u, ⟨hus, huM⟩, huU⟩ := hUd.inter_open_nonempty _ (ψ.isOpen_inter_preimage hMo) hne2
    have hvM := hMsub huM
    apply hvM.1
    apply hzero (ψ u) (hball hvM.2)
    rw [ψ.left_inv hus]
    exact huU
  obtain ⟨G0, hG0an, hG0eq⟩ := exists_re_of_levi_zero hr hd2 hlevi
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) r, ψ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxj, Metric.mem_ball_self hr⟩, fun y => G0 (ψ y), ?_, ?_⟩
  · exact holoOn_of_compat (isCompatChart_chart A j) Set.inter_subset_left (fun y hy => hG0an _ hy.2)
  · intro y hy
    have h := hG0eq (ψ y) hy.2
    simp only [hdd, ψ.left_inv hy.1] at h
    exact h

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RSnc
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_snc : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L₀ : LocPot X) (s₀ : X → X → ℂ) (n₀ : ℕ) (m₀ : Fin n₀ → ℕ) (W₀ : Fin n₀ → Set X) (L : LocPot X) (s : X → X → ℂ), IsSNC A L₀ s₀ m₀ W₀ → IsPotential A L → IsSection A L s → bdry s ⊆ {x | s₀ x x = 0} → (∀ x x', ∀ y ∈ L₀.U x ∩ L₀.U x', (s₀ x y = 0 ↔ s₀ x' y = 0)) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set X), IsSNC A L s m W := by
  intro e X _ _ _ A L₀ s₀ n₀ m₀ W₀ L s h₀ hL hs hb hz
  exact CSnc.snc_of_loc hL hs (CSnc.exists_loc h₀ hs hb hz)

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwOk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_ok : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  intro E _ _ _ H D l B _ b S s o g a
  obtain ⟨hm1, hm2⟩ := tw_mb E H l g
  refine ⟨fun x hx => o.eta_ker _ (tw_sub _ g.s D.La (a.a l.M) l.Mb hm1.le x hx), fun k _ _ x β hx => ?_⟩
  obtain ⟨hd, I, h1, h2, h3⟩ := o.geom k x β hx
  obtain ⟨J, hJ1, hJ2⟩ := tw_tate E H D g a k _ _ _ I
  refine ⟨tw_det E H D g S _ _ k x _ hd, J, by rw [hJ1]; exact h1, fun y => ?_, fun y hy => ?_⟩
  · rw [hJ2]
    exact h2 _
  · rw [hJ2]
    exact h3 _ (tw_sub _ g.s D.La (a.a l.M) _ hm2.le y hy)

end PositivityTheory.UnitarySelfGeneration
end

