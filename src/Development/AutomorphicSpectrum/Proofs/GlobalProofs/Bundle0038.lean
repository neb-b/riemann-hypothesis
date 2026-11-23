module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SpecialLinearMulApplyZeroZero
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PolyGrowthOfIsometricOnK
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AlmostIsomOfGrowth
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SecondCountableGrp
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticOnUJOfWordBound
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Glob.CharAF

theorem real_char (f : AddChar ℝ ℂ) (hf : Continuous f) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ α : ℝ, ∀ t : ℝ, f t = Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := by
  have hne : ∀ t, f t ≠ 0 := fun t h => by
    have := hn t
    simp [h] at this
  let χ : AddChar ℝ ℂˣ :=
    { toFun := fun t => Units.mk0 (f t) (hne t)
      map_zero_eq_one' := Units.ext (by simp)
      map_add_eq_mul' := fun a b => Units.ext (by simp [AddChar.map_add_eq_mul]) }
  have hχ : Continuous χ := Units.isEmbedding_val₀.continuous_iff.2 hf
  obtain ⟨s, hs, -⟩ := GroundTheory.Global.existsUnique_addChar_real_units χ hχ
  have hs' : ∀ t : ℝ, f t = Complex.exp (s * t) := hs
  have hre : s.re = 0 := by
    have h1 := hn 1
    rw [hs' 1, Complex.norm_exp] at h1
    simpa using h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨s.im / (2 * Real.pi), fun t => ?_⟩
  rw [hs' t]
  congr 1
  have hs2 : s = (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  push_cast
  rw [hs2]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]
  field_simp
  simp
  ring

theorem pi_char {ι : Type} [Fintype ι] [DecidableEq ι] (g : AddChar (ι → ℝ) ℂ) (hg : Continuous g)
    (hn : ∀ x, ‖g x‖ = 1) :
    ∃ α : ι → ℝ, ∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * x w : ℝ) : ℂ)) := by
  have key : ∀ w, ∃ α : ℝ, ∀ t : ℝ, g (Pi.single w t) =
      Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := fun w =>
    real_char (g.compAddMonoidHom (AddMonoidHom.single (fun _ => ℝ) w))
      (show Continuous (fun t : ℝ => g (Pi.single w t)) from hg.comp (continuous_pi fun j => by
        by_cases h : j = w
        · subst h
          simp only [Pi.single_eq_same]
          exact continuous_id
        · simpa [Pi.single_apply, h] using continuous_const)) (fun t => hn _)
  choose α hα using key
  refine ⟨α, fun x => ?_⟩
  have hx : x = ∑ w, Pi.single w (x w) := (Finset.univ_sum_single x).symm
  have hsum : ∀ s : Finset ι, g (∑ w ∈ s, Pi.single w (x w)) = ∏ w ∈ s, g (Pi.single w (x w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx]
  rw [hsum, Finset.prod_congr rfl fun w _ => hα w (x w), ← Complex.exp_sum, ← Finset.mul_sum]
  push_cast
  rfl

theorem places_indep {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (β : InfinitePlace F → ℝ)
    (h : ∀ c : F, ∑ w, β w * ρ w c = 0) : β = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      exact congrArg (fun f : F →* ℝ => ((f x : ℝ) : ℂ)) hww
    rw [← InfinitePlace.mk_embedding w, h1, InfinitePlace.mk_embedding]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  funext w
  refine Fintype.linearIndependent_iff.1 hli β ?_ w
  funext c
  simpa using h c

theorem exists_dual {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (htr : ∀ z : F, ∑ w, ρ w z = ((Algebra.trace ℚ F z : ℚ) : ℝ))
    (α : InfinitePlace F → ℝ) (N : ℕ) (hN : 0 < N)
    (hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n) :
    ∃ a : F, ∀ w, α w = ρ w a := by
  have hrat : ∀ c : F, ∃ q : ℚ, ∑ w, α w * ρ w c = q := by
    intro c
    obtain ⟨y, hy, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, (r : F) = (y : F) * c :=
      ⟨IsIntegralClosure.mk' (𝓞 F) (y • c) hyi,
        (IsIntegralClosure.algebraMap_mk' (𝓞 F) (y • c) hyi).trans (by simp)⟩
    obtain ⟨n, hn⟩ := hint r
    refine ⟨n / (N * y), ?_⟩
    have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 : ∑ w, α w * ρ w ((N : F) * (r : F)) = N * y * ∑ w, α w * ρ w c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hr]
      simp only [map_mul, map_natCast, map_intCast]
      ring
    rw [h1] at hn
    push_cast
    field_simp
    linarith
  choose q hq using hrat
  let L : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun x y => by
        have : ((q (x + y) : ℚ) : ℝ) = ((q x + q y : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, ← hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [map_add (f := _)]
          ring
        exact_mod_cast this
      map_smul' := fun t x => by
        have : ((q (t • x) : ℚ) : ℝ) = ((t * q x : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          have : t • x = (t : F) * x := by simp [Algebra.smul_def]
          rw [this, map_mul, map_ratCast]
          ring
        exact_mod_cast this }
  let a : F := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm L
  have ha : ∀ c, q c = Algebra.trace ℚ F (a * c) := by
    intro c
    have h1 := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ F) (m := a) (n := c)
    rw [LinearEquiv.apply_symm_apply, Algebra.traceForm_apply] at h1
    exact h1
  refine ⟨a, fun w => ?_⟩
  have h0 : (fun w => α w - ρ w a) = 0 := by
    refine places_indep ρ hρ _ fun c => ?_
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hq c, ha c, ← htr (a * c)]
    simp [map_mul]
  have h1 := congrFun h0 w
  simpa [sub_eq_zero] using h1

theorem exists_char_data : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) ∧ ∃ ψf : AddChar (Af F) ℂ, GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf ∧ ∀ y : Af F, ψ (pairA F 0 y) = ψf (algebraMap F (Af F) a * y) := by
  intro F _ _ hF ρ e hρ he heρ ψ hψ
  classical
  have htr := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ
  have hes : Continuous e.toEquiv.symm := (Equiv.continuous_symm_iff e.toEquiv).2 he.isOpenMap

  let φ : (InfinitePlace F → ℝ) →+ AF F :=
    { toFun := fun x => pairA F (e.symm x) 0
      map_zero' := by
        rw [map_zero]
        rfl
      map_add' := fun x y => by
        rw [map_add (f := _)]
        exact Prod.ext rfl (add_zero _).symm }
  have hφ : Continuous φ := (hes.prodMk continuous_const : Continuous fun x => (e.symm x, (0 : Af F)))
  obtain ⟨α, hα⟩ := pi_char (ψ.compAddMonoidHom φ) (hψ.1.comp hφ) (fun x => hψ.2.1 _)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * e x w : ℝ) : ℂ)) := fun x => by
    have := hα (e x)
    simpa [φ] using this
  have hsplit : ∀ c : F, ψ (pairA F (algebraMap F (Ainf F) c) 0) *
      ψ (pairA F 0 (algebraMap F (Af F) c)) = 1 := fun c => by
    rw [← AddChar.map_add_eq_mul, ← hψ.2.2.1 c]
    exact congrArg ψ (Prod.ext (add_zero _) (zero_add _))

  obtain ⟨N, hN, hNU⟩ := (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.2.2.1 _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  have hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n := by
    intro r
    have hr : algebraMap F (Af F) (r : F) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F :=
      ((_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩
    have h1 : ψ (pairA F 0 (algebraMap F (Af F) ((N : F) * (r : F)))) = 1 := by
      have := hNU _ hr
      rw [map_mul, map_natCast]
      exact this
    have h2 := hsplit ((N : F) * (r : F))
    rw [h1, mul_one, hinf, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : ((∑ w, α w * e (algebraMap F (Ainf F) ((N : F) * (r : F))) w : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hI
      rw [hn]
      ring
    simp only [heρ] at h3
    exact_mod_cast h3
  obtain ⟨a, ha⟩ := exists_dual ρ hρ htr α N hN hint
  have hinf' : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ)) := fun x => by
    rw [hinf]
    simp only [ha]
  have hfin : ∀ c : F, ψ (pairA F 0 (algebraMap F (Af F) c)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ)) := fun c => by
    have h1 := hsplit c
    have h2 : ((∑ w, ρ w a * e (algebraMap F (Ainf F) c) w : ℝ) : ℂ) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ) := by
      have h3 := htr (a * c)
      simp only [map_mul] at h3
      simp only [heρ]
      rw [h3]
      push_cast
      rfl
    rw [hinf', h2] at h1
    rw [neg_mul, Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : ∀ x : Ainf F, ψ (pairA F x 0) = 1 := fun x => by
      rw [hinf']
      simp
    have h2 : ∀ y : Af F, ψ (pairA F 0 y) = 1 := by
      intro y
      have hc : Continuous fun y : Af F => ψ (pairA F 0 y) := hψ.1.comp hp
      refine (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.1.induction_on y (isClosed_eq hc continuous_const) fun c => ?_
      rw [hfin]
      simp
    obtain ⟨z, hz⟩ := hψ.2.2.2
    apply hz
    have h3 : z = pairA F z.1 0 + pairA F 0 z.2 := Prod.ext (add_zero _).symm (zero_add _).symm
    rw [h3, AddChar.map_add_eq_mul, h1, h2, one_mul]

  let ψf : AddChar (Af F) ℂ :=
    { toFun := fun y => ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * y))
      map_zero_eq_one' := by
        rw [mul_zero]
        exact ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => by
        rw [mul_add, ← AddChar.map_add_eq_mul]
        exact congrArg ψ (Prod.ext (add_zero _).symm rfl) }
  refine ⟨a, ha0, hinf', ψf, ⟨?_, fun b => ?_⟩, fun y => ?_⟩
  · exact hψ.1.comp (hp.comp (continuous_const.mul continuous_id))
  · show ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) b)) = _
    rw [← map_mul, hfin, mul_inv_cancel_left₀ ha0]
  · show _ = ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * (algebraMap F (Af F) a * y)))
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]

end GlobalTheory.CompanionTheory.Glob.CharAF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdmissibleOfIwasawaDecomposition
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem isotypic : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic.exists_isotypic_sum

theorem garding : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hK : ∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u)) → ∀ y ∈ Y, T y ∈ Y), ∀ v ∈ Y, IsSmoothVec G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard.smooth_of_commutant_stable

theorem growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hK : ∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖), ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth.polyGrowth_of_isometric_on_K

theorem volume : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume.integrable_wt_rpow_neg

theorem almost_of_growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hg : ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖) (hv : ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv), AlmostIsom (UJset ε) π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Growth.almostIsom_of_growth

theorem iwa_levi : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W), g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi.exists_unitary_iwasawa_leviOne

theorem admissible_of_iwasawa_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) (hU : IsURepOn G π) (hirr : IsIrredOn G π), IsAdmOn G π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted.isAdmOn_of_iwasawa

theorem smooth_deriv : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec

theorem smooth_lin : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear

theorem inv_basis : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal

theorem delta_comm : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G) (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l) {v : H} (hv : IsSmoothVec G π v), π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.sumSquares_comm

theorem word_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta.word_bound_of_delta

theorem analytic_uj : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H} (hs : IsSmoothVec (UJset ε) π v) (hw : WordBound (UJset ε) π v) (w : H), GlobalTheory.Published.AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.AnalyticWords.analyticOnUJ_of_wordBound

theorem one_param : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H), AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam.analytic_coeff

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_word_of_adm {G : Set (Matrix (Fin n) (Fin n) ℂ)} [CompleteSpace H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hA : IsAdmOn G π) (hQ : AlmostIsom G π) {v : H}
    (hv : IsKFinOn G π v) : IsSmoothVec G π v ∧ WordBound G π v := by
  obtain ⟨hrep, hc, hK, -⟩ := id hA
  obtain ⟨Y, hYf, hvY, hYK, hD⟩ := isotypic hG hA hv
  have hYs : ∀ y ∈ Y, IsSmoothVec G π y := garding hG hcl hrep hc hK Y fun T hT y hy => by
    have := hD ((T : H →ₗ[ℂ] H).comp Y.subtype) (fun k hk y y' e => by
      show T (y' : H) = π k (T (y : H))
      rw [e, hT k hk]) ⟨y, hy⟩
    exact this
  obtain ⟨d, b, hb, hli, hsp, hinv⟩ := inv_basis hG
  refine ⟨hYs v hvY, word_of_delta hG hrep hc hQ b hb hli hsp Y hYs ?_ v hvY⟩
  have hsm : ∀ (y : H), IsSmoothVec G π y → ∀ i, IsSmoothVec G π (dRep π (b i) (dRep π (b i) y)) := fun y hy i =>
    (smooth_deriv hG hrep (smooth_deriv hG hrep hy (hb i)).2 (hb i)).2
  let Dl : Y →ₗ[ℂ] H :=
    { toFun := fun y => ∑ i, dRep π (b i) (dRep π (b i) (y : H))
      map_add' := fun x y => by
        refine Finset.sum_congr rfl (fun i _ => ?_) |>.trans Finset.sum_add_distrib
        have hx := hYs x x.2
        have hy := hYs y y.2
        rw [Submodule.coe_add, (smooth_lin hG hrep hx hy (hb i) (hb i)).2.1,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hy (hb i)).2
            (hb i) (hb i)).2.1]
      map_smul' := fun c x => by
        have hx := hYs x x.2
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, (smooth_lin hG hrep hx hx (hb i) (hb i)).2.2,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hx (hb i)).2
            (hb i) (hb i)).2.2] }
  intro y hy
  refine hD Dl (fun k hk y y' e => ?_) ⟨y, hy⟩
  obtain ⟨O, hO, hkb⟩ := hinv k hk
  show ∑ i, dRep π (b i) (dRep π (b i) (y' : H)) = π k (∑ i, dRep π (b i) (dRep π (b i) (y : H)))
  rw [e, delta_comm hG hrep b hb hk.1 O hO hkb (hYs y y.2)]

theorem isClosed_UJset (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem almostIsom_of_unitary {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn G π) : AlmostIsom G π := by
  refine ⟨fun x y => ⟪x, y⟫_ℂ, 1, 1, 0, one_pos, zero_le_one, le_refl _, fun x y z => inner_add_right x y z,
    fun c x y => inner_smul_right x y c, fun x y => (inner_conj_symm y x).symm, fun x => ?_, fun x y => ?_,
    fun X hX t x => ?_⟩
  · show 1 * ‖x‖ ^ 2 ≤ (⟪x, x⟫_ℂ).re
    rw [one_mul]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).ge
  · show ‖⟪x, y⟫_ℂ‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [one_mul]; exact norm_inner_le_norm x y
  · have h (u : H) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
    show (⟪π _ x, π _ x⟫_ℂ).re ≤ _ * (⟪x, x⟫_ℂ).re
    simp only [h, hU.2.1 _ (hX t) x]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open HCA

theorem admissibleCoefficientsAnalytic : GlobalTheory.Published.AdmissibleCoefficientsAnalytic := by
  intro n ε H _ _ _ π hπ v w hv _
  have hG := GlobalTheory.HCUnitary.isLinRed_UJset ε
  have hA : IsAdmOn (UJset ε) π := GlobalTheory.HCUnitary.isAdmOn_iff.2 hπ
  have hQ : AlmostIsom (UJset ε) π :=
    almost_of_growth hπ.1 hπ.2.1 (growth hπ.1 hπ.2.1 hπ.2.2.1) (volume ε)
  have hv' : IsKFinOn (UJset ε) π v := by
    obtain ⟨S, h1, h2, h3⟩ := hv
    exact ⟨S, h1, h2, GlobalTheory.HCUnitary.isKStable_iff.2 h3⟩
  obtain ⟨hs, hw⟩ := smooth_word_of_adm hG (isClosed_UJset ε) hA hQ hv'
  exact analytic_uj hπ.1 hπ.2.1 hs hw w

theorem leviSubmoduleDense : GlobalTheory.Published.LeviSubmoduleDense := by
  intro n ε a j W hW hj V _ _ _ σ hU hI S hS hK hL
  obtain ⟨hG, hexp⟩ := GlobalTheory.LeviPolar.isLinRed_leviOne n ε a j W hW hj
  have hA : IsAdmOn (mats (leviOne ε W)) σ := admissible_of_iwasawa_decomposition hG (iwa_levi hW hj) hU hI
  have hQ := almostIsom_of_unitary hU
  have hcl : IsClosed (mats (leviOne ε W)) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isClosedMap _ (isClosed_leviOne hW hj)
  have keep : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
      ∀ v ∈ S.topologicalClosure, σ (NormedSpace.exp X) v ∈ S.topologicalClosure := fun X hX => by
    have := GlobalTheory.LeviDense.oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) (by simp [hU.1.1])
      (fun s t => by
        rw [← hU.1.2 _ (hX s) _ (hX t), add_smul,
          Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
      (hL X hX)
      (fun v hv w => by
        obtain ⟨h1, h2⟩ := smooth_word_of_adm hG hcl hA hQ (GlobalTheory.LeviDense.isKFinOn_of_isKFinIn (hK v hv))
        exact one_param hG hU h1 h2 hX w) 1
    simpa only [one_smul] using this
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure (fun g hg v hv => by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hexp g hg
    rw [hU.1.2 _ (by simpa using hX 1) _ (by simpa using hY 1)]
    exact keep X hX _ (keep Y hY v hv)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ S.le_topologicalClosure)) hS
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem harishChandra_analyticity_density : GlobalTheory.Published.HarishChandraAnalyticity :=
  ⟨admissibleCoefficientsAnalytic, leviSubmoduleDense⟩

end GlobalTheory.CompanionTheory.Hypotheses₂

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBridge

theorem finEps_shift : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) :=
  fun _ _ _ χ a s => GlobalTheory.HeckeEpsAbs.finEps_eq χ a s

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicLocalSectionsCompatible
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem gagaSections_pure : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), IsProper s → SmoothOfRelativeDimension D s → ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ : L.Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i → valAt' x (L.U i) (σ.f i) = h i x := by
  intro X s D hp hs L hL h hh hg
  obtain ⟨σ, hσ, e⟩ := _root_.GlobalTheory.CompanionTheory.Gaga.exists_mem_holSec X s D hs (AnRead.all s (RingHom.id ℂ) D) L hL h hh hg
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper X s D hs hp (AnRead.all s (RingHom.id ℂ) D) L hL σ hσ
  refine ⟨t, fun i x hx hU => ?_⟩
  have hx' : x ≫ s = spMap (RingHom.id ℂ) := by
    rw [hx, spMap]; exact (by simp)
  let y : CxPts s (RingHom.id ℂ) := ⟨x, hx'⟩
  have hy : y ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hU
  have h1 := e i y hy
  rw [← ht] at h1
  exact h1

end GlobalTheory.CompanionTheory.Gaga
end

