module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MapRestrictIntH
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.ExistsFinsetOfCofinite
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetLatHLoc
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latH_loc (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc := (GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) b n).continuous
  have : (latH σ b v n : Set (HermR (Fv F v) σ n)) =
      (GlobalTheory.CompanionTheory.SW.HermSd.hermVec (Fv F v) σ b n) ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    Set.ext fun S => (HS.mem_latH_iff_vec σ b n v S).trans ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [this]
  exact hc.measurable (MeasurableSet.univ_pi fun _ => hO.measurableSet)

theorem measurableSet_intHR (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (HS.intHR σ b n S) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  have : HS.intHR σ b n S =
      ⋂ v, ⋂ (_ : v ∉ S), (HS.hV σ v) ⁻¹' (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
    ext y
    simp only [HS.intHR, Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  exact (HS.continuous_hermV σ hCM n v).measurable (measurableSet_latH_loc σ hCM b n v)

theorem herm_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n d : ℕ)
    (bs : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (hν : SdHerm F E σ (AF F) ψ n ν)
    (νi : Measure (HermR (Ainf F) σ n)) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∀ (gi : HermR (Ainf F) σ n → ℂ) (g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
        (∀ v ∈ S, AEStronglyMeasurable (g v) (νv v)) →
        ∫ b in UH σ bs n S, gi (hermInf σ b) * ∏ v ∈ S, g v (hermV σ v (hermFin σ b)) ∂ν =
          (∫ x, gi x ∂νi) * ∏ v ∈ S, ∫ x, g v x ∂(νv v) := by
  classical
  obtain ⟨⟨laminf, hinf⟩, hlamE⟩ := _root_.GlobalTheory.CompanionTheory.SW.StdEx.exists_std F
  choose lam hlam using hlamE
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  obtain ⟨cinf, c, hU, hci, hcv⟩ := GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord F E σ hCM d bs laminf lam hinf hlam ψ hψ n
  have eνi : νi = cinf • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n := (hci νi).1 hνi
  have eνv : ∀ v, νv v = c v • GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := fun v => (hcv v (νv v)).1 (hνv v)
  have hfin : {v | ¬ c v = 1}.Finite := Filter.eventually_cofinite.1 hU.1
  refine ⟨hfin.toFinset, fun S hS gi g hg => ?_⟩
  have hprod : cinf * ∏ v ∈ S, c v = 1 := by
    have h2 := hU.2
    rwa [finprod_eq_prod_of_mulSupport_subset c (s := S) fun v hv => hS (hfin.mem_toFinset.2 hv)] at h2
  have hcS : ∀ v ∈ S, c v ≠ 0 := fun v hv h0 => by
    rw [Finset.prod_eq_zero hv h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  have hSF : ∀ v, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n) := fun v =>
    haveI : SigmaFinite (lam v) := Measure.IsAddHaarMeasure.sigmaFinite (lam v)
    HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) bs n).homeomorph _).toMeasurableEquiv
      (GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Fv F v) bs n (lam v))
  haveI : ∀ v : S, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := fun v => hSF v.1
  have hmp := HS.db_split σ hCM ψ hψ n ν hν bs laminf hinf lf hlf h1
  obtain ⟨-, -, -, -, -, -, -, -, hme0, -⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod F E σ hCM n ν hν.1
  have hme : MeasurableEmbedding (fun S : HermR (AF F) σ n => (HS.hInfR σ S, HS.hFinR σ S)) := hme0
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) := by
    obtain ⟨hH, -⟩ := hinf
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
    have hmpI := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Ainf F) bs n laminf
    haveI : SigmaFinite laminf := Measure.IsAddHaarMeasure.sigmaFinite laminf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Ainf F) bs n).homeomorph _).toMeasurableEquiv hmpI
    infer_instance
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n) := by
    obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    haveI : BorelSpace (Af F) := ⟨rfl⟩
    have hmpF := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Af F) bs n lf
    haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Af F) bs n).homeomorph _).toMeasurableEquiv hmpF
    infer_instance

  set fS : HermR (Af F) σ n → ℂ := fun y => ∏ v ∈ S, g v (HS.hV σ v y) with hfS
  set Φ : HermR (Ainf F) σ n × HermR (Af F) σ n → ℂ :=
    fun p => gi p.1 * (HS.intHR σ bs n S).indicator fS p.2 with hΦ
  have e1 : ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν =
      ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν := by
    rw [← integral_indicator (measurableSet_UH σ hCM bs n S)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ UH σ bs n S
    · have hb' : HS.hFinR σ b ∈ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_mem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_mem hb']
    · have hb' : HS.hFinR σ b ∉ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_notMem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_notMem hb', mul_zero]
  have e2 : ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν =
      (∫ x, gi x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) *
        ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n := by
    rw [hmp.integral_comp hme Φ]
    exact integral_prod_mul gi _
  have hAE : AEStronglyMeasurable (fun x : ∀ v : S, HermR (Fv F v.1) σ n => ∏ v : S, g v.1 (x v))
      (Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
    have := Finset.aestronglyMeasurable_prod (μ := Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n)
      (f := fun (v : S) (x : ∀ v : S, HermR (Fv F v.1) σ n) => g v.1 (x v)) Finset.univ (fun v _ => by
        have hgv : AEStronglyMeasurable (g v.1) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
          have h0 := hg v.1 v.2
          rw [eνv v.1] at h0
          refine h0.mono_ac (fun s hs => ?_)
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hs
          exact hs.resolve_left (by exact_mod_cast hcS v.1 v.2)
        exact hgv.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ v))
    convert this using 1
    funext x
    simp [Finset.prod_apply]
  have e3 : ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
      ∏ v ∈ S, ∫ x, g v x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := by
    rw [integral_indicator (measurableSet_intHR σ hCM bs n S)]
    have hρ : Measurable (fun y (v : S) => HS.hV σ v.1 y) :=
      Measurable.of_eval fun v => (HS.continuous_hermV σ hCM n v.1).measurable
    have hmap := HS.map_restrict_intH σ hCM bs lam hlam lf hlf h1 n S
    have e4 : ∫ y in HS.intHR σ bs n S, fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
        ∫ x, ∏ v : S, g v.1 (x v) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n).restrict (HS.intHR σ bs n S)).map
          (fun y (v : S) => HS.hV σ v.1 y) := by
      rw [integral_map hρ.aemeasurable (by rw [hmap]; exact hAE)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfS]
      rw [← Finset.prod_coe_sort S]
    rw [e4, hmap, integral_fintype_prod_eq_prod (fun (v : S) => g v.1), ← Finset.prod_coe_sort S]
  show ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν = _
  rw [e1, e2, e3, eνi, integral_smul_nnreal_measure]
  simp only [eνv, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [Finset.prod_mul_distrib]
  have hprodC : ((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ) = 1 := by
    have := congrArg (fun x : NNReal => ((x : ℝ) : ℂ)) hprod
    push_cast at this
    exact this
  have key : ∀ (a k q p : ℂ), k * q = 1 → a * p = (k * a) * (q * p) := fun a k q p h => by
    linear_combination (-(a * p)) * h
  exact key _ _ _ _ hprodC

end PositivityTheory.SiegelWeilFormula.GFac

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.WXMain
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.W

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix

theorem whitGenLtOf : LocFin2 → UnrWhit → RealWhit → FactorX → PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA → WhitGenLt := by
  intro hLoc hUnr hReal hFac hSDL F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok hrange _ ht
    μH 𝓕 hμH h𝓕
  have hlt : n < M := hok
  have hra : n + 2 ≤ M ∨ PositivityTheory.PfSWUS.HMass.IsAnisoH σ J := by
    rcases hrange with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx0 => hx (h x hx0)
  rw [one_mul]
  obtain ⟨t, ht⟩ := ht
  have hT := hD.hT

  have h0 := hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs 0 0 Φf Φv isSchwartzInf_zero hD.pure
    (fun X => by simp)
  have h1 := ((h0.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr
  obtain ⟨μi, hμi⟩ := h1.1
  obtain ⟨νi, hνi⟩ := (h1.2 μi hμi).1
  obtain ⟨μv, hμv⟩ := ((h1.2 μi hμi).2 νi hνi).1
  obtain ⟨νv, hνv⟩ := (((h1.2 μi hμi).2 νi hνi).2 μv hμv).1

  have hR := hReal F E σ hD.cm M J hD.herm n hlt ψ hD.chr ι θ l hD.places ε fr hD.frames g P μi νi hμi hνi

  have h2 := hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs Φ (phiInf θ l fr g P) Φf Φv hR.1 hD.pure hD.prod
  obtain ⟨ginf, gv, hdinf, hdv, hmult, hmean⟩ :=
    (((((h2.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr).2 μi hμi).2 νi hνi).2 μv hμv |>.2 νv hνv
  obtain ⟨Wi, hWi, hWi0, ti, hti⟩ := hR.2 ginf hdinf (hermOf (Ainf F) σ T hT) (hermOf_unit σ T hT hD.det _)

  have hL := fun v => hLoc F E σ hD.cm M J hD.herm n hlt ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v)
    (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) (gv v) (hdv v) (hermOf (Fv F v) σ T hT)
    (hermOf_unit σ T hT hD.det _)
  choose Wv hWv hWv0 tv htv using hL

  obtain ⟨tu, hU⟩ := hUnr F E σ hD.cm M J hD.herm n hlt T hT hD.det d bs ψ hD.chr
  have hev := (hU.and hD.std).and hD.pure.2.1
  obtain ⟨S, hSout⟩ := exists_finset_of_cofinite hev
  choose! e he using fun v (hv : v ∉ S) => (hSout v hv).1.1
  have hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) ∧
      ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) =
        unrP n M (e v) (Ideal.absNorm v.asIdeal) z := by
    intro v hv z hz
    obtain ⟨⟨-, hs1, hs2⟩, hpv⟩ := hSout v hv
    have hL12 : L₂ v = L₁ v := SetLike.coe_injective (hs2.trans hs1.symm)
    rw [hL12, hpv]
    exact he v hv (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz

  have hgv : ∀ v, v ∉ S →
      gv v (hermOf (Fv F v) σ T hT) = unrP n M (e v) (Ideal.absNorm v.asIdeal) (((M : ℂ) - n) / 2) := by
    intro v hv
    have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      omega
    have heq := eq_of_eqOn_right (hWv v) (unramifiedPart_differentiable n M (e v) _ hq) (max (tv v) tu) fun z hz =>
      ((htv v z (lt_of_le_of_lt (le_max_left _ _) hz)).2).trans
        ((hPv v hv z (lt_of_le_of_lt (le_max_right _ _) hz)).2)
    rw [← hWv0 v, heq]
  obtain ⟨D, hDd, hDp⟩ := unr_prod (F := F) n M (↑S : Set (HeightOneSpectrum (𝓞 F))) e
  have hs0 : (0 : ℝ) < (((M : ℂ) - n) / 2).re := by
    have : (n : ℝ) < M := by exact_mod_cast hlt
    have h : (((M : ℂ) - n) / 2) = ((((M : ℝ) - n) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.ofReal_re]
    linarith
  let U : Set ℂ := {z | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let G : ℂ → ℂ := fun z => Wi z * ((∏ v ∈ S, Wv v z) * D z)
  have hGd : DifferentiableOn ℂ G U :=
    hWi.differentiableOn.mul ((DifferentiableOn.fun_finsetProd fun v _ => (hWv v).differentiableOn).mul hDd)

  have hGs0 : G (((M : ℂ) - n) / 2) = meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) := by
    have hp := hasProd_split (fun v => gv v (hermOf (Fv F v) σ T hT)) S (D (((M : ℂ) - n) / 2)) (by
      convert hDp _ hs0 using 1
      funext v
      exact hgv v.1 v.2)
    show Wi _ * ((∏ v ∈ S, Wv v _) * D _) = _
    rw [hmean, hp.tprod_eq, hWi0, Finset.prod_congr rfl fun v _ => hWv0 v]

  have hright : Set.EqOn G
      (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)
      (rightOf (|t| + |ti| + |tu| + ∑ v ∈ S, |tv v|)) := by
    intro z hz
    have hz' : |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| < z.re := hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    have zt : t < z.re := by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]
    have zti : ti < z.re := by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]
    have ztu : tu < z.re := by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]
    have z0 : 0 < z.re := by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have ztv : ∀ v ∈ S, tv v < z.re := fun v hv => by
      have := Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv
      linarith [le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) := by
      intro v
      by_cases hv : v ∈ S
      · exact (htv v z (ztv v hv)).1
      · exact (hPv v hv z ztu).1
    have hF := hFac F E σ M n d J T bs ψ ι θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z
      (ht z zt) (hti z zti).1 hint
    have hp := hasProd_split (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z b ∂(νv v)) S (D z) (by
      convert hDp z z0 using 1
      funext v
      exact (hPv v.1 v.2 z ztu).2)
    have hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v)
        (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop
        (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
          (T.map (inclR (Fv F v))) z b ∂(νv v)) * D z)) := hp
    have hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi =
        Wi z := (hti z zti).2.symm
    rw [hIi] at hF
    have hu := tendsto_nhds_unique hF (hlim.const_mul (Wi z))
    show Wi z * ((∏ v ∈ S, Wv v z) * D z) = _
    rw [Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]
    exact hu.symm
  refine ⟨G, ⟨U, hs0, ⟨⟨0, fun z hz => hz⟩, fun s hs r hr => ?_⟩, (hGd.analyticOnNhd hUo).meromorphicOn,
    ⟨_, hright⟩⟩, hGd.analyticOnNhd hUo _ hs0, hGs0⟩
  have hs' : 0 < s.re := hs
  show 0 < (s + r).re
  simp
  linarith

end PositivityTheory.SiegelWeilFormula.Gen.W

theorem PositivityTheory.SiegelWeilFormula.Gen.whitGenLtOf : PositivityTheory.SiegelWeilFormula.Gen.LocFin2 → PositivityTheory.SiegelWeilFormula.Gen.UnrWhit →
    PositivityTheory.SiegelWeilFormula.Gen.RealWhit → PositivityTheory.SiegelWeilFormula.Gen.FactorX → PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA →
    PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt :=
  PositivityTheory.SiegelWeilFormula.Gen.W.whitGenLtOf

end
end

