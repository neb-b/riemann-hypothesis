module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ImportsAlt
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.proj :
    UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Proj := by
  intro hE E _ _ _ n U U' C sU sU' sC h0 hne hle hs
  have sup : ∀ T : Module.End ℂ (cuspForms E n), (∀ φ ∈ U, T φ ∈ U) → (∀ φ ∈ U', T φ ∈ U') →
      ∀ φ ∈ U ⊔ U', T φ ∈ U ⊔ U' := fun T h h' φ hφ => by
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hφ
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h u hu) (h' x hx)
  refine ⟨C ⊓ (U ⊔ U'), inf_le_left, fun e => hne (eq_bot_iff.2 fun x hx => ?_),
    ⟨fun X φ h => ⟨sC.ρ X φ h.1, sup _ (sU.ρ X) (sU'.ρ X) φ h.2⟩,
      fun X φ h => ⟨sC.σ X φ h.1, sup _ (sU.σ X) (sU'.σ X) φ h.2⟩,
      fun X φ h => ⟨sC.τ X φ h.1, sup _ (sU.τ X) (sU'.τ X) φ h.2⟩⟩,
    hs.mono fun w ⟨B, h1, h2⟩ => ⟨B, h1, fun c hc hK => ?_⟩⟩
  · obtain ⟨u, hu, c, hc, e'⟩ := Submodule.mem_sup.1 (hle hx)
    have h1 : c ∈ C ⊓ (U ⊔ U') := ⟨hc, by
      rw [show c = -u + x by rw [← e']; abel]
      exact Submodule.add_mem_sup (U.neg_mem hu) hx⟩
    rw [e, Submodule.mem_bot] at h1
    rw [h1, add_zero] at e'
    rw [← h0]
    exact ⟨e' ▸ hu, hx⟩
  · obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hc.2
    have ev : ∀ (φ : cuspForms E n) k g, (finRepCusp E n k φ).1 g = φ.1 (g * finGL E n k) := fun φ k g => by
      rw [← Fb.finEmb_eq]
      rfl
    have key : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), finRepCusp E n (locGL E n w k) u = u ∧ finRepCusp E n (locGL E n w k) x = x := by
      intro k hk
      have e : finRepCusp E n (locGL E n w k) (u + x) = u + x :=
        Subtype.ext (funext fun g => (ev _ _ g).trans (hK g k hk))
      rw [map_add (f := _)] at e
      have e2 : finRepCusp E n (locGL E n w k) u - u = x - finRepCusp E n (locGL E n w k) x := by
        rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
      have m : finRepCusp E n (locGL E n w k) u - u ∈ U ⊓ U' :=
        ⟨U.sub_mem (sU.τ _ u hu) hu, e2 ▸ U'.sub_mem hx (sU'.τ _ x hx)⟩
      rw [h0, Submodule.mem_bot] at m
      exact ⟨sub_eq_zero.1 m, (sub_eq_zero.1 (e2.symm.trans m)).symm⟩
    have a := h1 (-u) (U.neg_mem hu) fun g k hk => by
      rw [← ev, map_neg, (key k hk).1]
    have b := h2 x hx fun g k hk => by rw [← ev, (key k hk).2]
    have e : (u + x).1 = x.1 - (-u).1 := by
      rw [← Submodule.coe_sub, sub_neg_eq_add, add_comm]
    rw [e]
    exact (hE E n w B _ b).2.2 _ a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.InKSMono
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

theorem UpperTheory.V.Af.StrongMultiplicityOne.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.SetUp := by
  intro hP hL hN E _ _ n U U' hs φ φ'
  classical
  have lev : ∀ φ : cuspForms E n, ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := fun φ => by
    obtain ⟨V, hV⟩ := (hN E n φ).1
    obtain ⟨S, hS⟩ := hL E n V
    exact ⟨S, fun g k hk => hV g k (hS k hk)⟩
  obtain ⟨S₁, h₁⟩ := lev φ
  obtain ⟨S₂, h₂⟩ := lev φ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ Sat w B U ∧ Sat w B U' := fun w => by
    by_cases hw : w ∈ hf.toFinset
    · exact ⟨0, fun h => absurd hw h⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hg, B, hB⟩ := hw
      exact ⟨B, fun _ => ⟨hg, hB⟩⟩
  choose B hB using hB
  refine ⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h),
    fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_right
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.NiceOf
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.niceOf :
    UpperTheory.V.Af.StrongMultiplicityOne.NiceOf := by
  intro E _ _ n φ
  have hl : ∃ V : OpenSubgroup (GL (Fin n) (Af E)), ∀ g, ∀ v ∈ V, φ.1 (g * finGL E n v) = φ.1 g := by
    obtain ⟨W, -, hW⟩ := exists_openSubgroup_rightInvariant φ.2.1.isSmooth φ.2.1.isKFinite
    refine ⟨W, fun g v hv => ?_⟩
    rw [← Fb.finEmb_eq]
    exact hW g v hv
  exact ⟨hl, fun h => ⟨φ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms h, φ.2.1.isLeftInvariant, φ.2.2, hl⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.NormTwist
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.normTwist :
    UpperTheory.V.Af.StrongMultiplicityOne.NormTwist := by
  intro E _ _ _ n hn π
  obtain ⟨κ, hκ⟩ := GlobalTheory.CuspRep.Central.exists_hasCentral E n π
  let z : {r : ℝ // 0 < r} →* (Ad E)ˣ :=
    (Reduction.posIdeleHom E).comp (Reduction.rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹)
  have hz : ∀ s, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) (z s) := fun s => Units.ext rfl
  have hc : Continuous z := Reduction.continuous_posIdeleHom.comp (Reduction.continuous_rpowHom _)
  have hm : ∀ s, GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n) = s := fun s => by
    have h := Reduction.detModule_centralSection (K := E) hn s
    rw [hz] at h
    refine Eq.trans (congrArg _ (Units.ext ?_)) h
    change _ = Matrix.det (Matrix.diagonal fun _ : Fin n => (z s).val)
    simp
  let ν : Formalism.L2.Host.HChar E := ⟨(κ⁻¹.1.comp z).comp (GroundTheory.Global.IdeleGroup.ideleModule E),
    (κ⁻¹.2.1.comp hc).comp GroundTheory.Global.IdeleGroup.continuous_ideleModule, fun k => by
      have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := E) k
      exact (congrArg (κ⁻¹.1.comp z) h).trans (map_one _)⟩
  refine ⟨ν, fun φ hφ s g => ?_⟩
  rw [hz, (hκ.twist ν).apply hφ]
  have e : (κ * ν ^ n).1 (z s) = 1 := by
    change κ.1 (z s) * (ν.1 ^ n) (z s) = 1
    rw [MonoidHom.pow_apply, ← map_pow]
    change κ.1 (z s) * (κ.1 (z (GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n))))⁻¹ = 1
    rw [hm, mul_inv_cancel]
  rw [e]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.OrthConv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem conv_left {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (f : GA E n → ℂ)
    (α : Lie E n → ℂ) (z : GA E n) (h : ∀ g, f (z * g) = f g) (g : GA E n) : Af.StrongMultiplicityOne.conv f α (z * g) = Af.StrongMultiplicityOne.conv f α g := by
  have e : chart f (z * g) = chart f g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, h]
    · rfl
  unfold Af.StrongMultiplicityOne.conv
  rw [e]

private theorem zero_of_sq {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (Reduction.normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (F : AdelicGLn.AdelicGL E n → ℂ) (hc : Continuous F) (C : ℝ) (hC : ∀ g, ‖F g‖ ≤ C)
    (h : IsLeftInvariant F)
    (h0 : ∫ q, starRingEnd ℂ (CuspidalSpectrum.cuspQuot h q) * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0) :
    ∀ y ∈ Reduction.normOneGL (K := E) (n := n), F y = 0 := by
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  have hq := CuspidalSpectrum.continuous_cuspQuot h hc
  have hb : ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun q => by
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    exact hC _
  have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2)
      (RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) :=
    Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb q) 2)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
  have h3 := MeasureTheory.QuasiMeasurePreserving.ae_eq_comp
    (RightCosetSpace.quasiMeasurePreserving_mk (Reduction.rationalGLOne (K := E) (n := n)) μ) h2
  have h4 := (Continuous.ae_eq_iff_eq μ (f := fun y : Reduction.normOneGL (K := E) (n := n) => ‖F y‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
  intro y hy
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h4 ⟨y, hy⟩))

theorem UpperTheory.V.Af.StrongMultiplicityOne.orthConv :
    UpperTheory.V.Af.StrongMultiplicityOne.OrthStep → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont → UpperTheory.V.Af.StrongMultiplicityOne.OrthConv := by
  intro hS hC E _ _ _ n μ _ φ φ' hφ hφ' ho β β' e
  obtain ⟨C, hb⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C', hb'⟩ := exists_norm_le_of_mem_centralCuspForms hφ'
  have l : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ.1 β) := fun γ g => conv_left _ _ _ (φ.2.1.isLeftInvariant γ) g
  have l' : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ'.1 β') := fun γ g => conv_left _ _ _ (φ'.2.1.isLeftInvariant γ) g
  obtain ⟨hc, D, hD⟩ := hC E n φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ β'
  have s1 : ∀ g, ∫ q, starRingEnd ℂ (quotTr φ g q) * CuspidalSpectrum.cuspQuot l' q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := fun g =>
    hS E n μ φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ φ'.2.1.isLeftInvariant (fun q => starRingEnd ℂ (quotTr φ g q))
      (Complex.continuous_conj.comp (continuous_quotTr φ g))
      ⟨C, fun q => by
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Complex.norm_conj]
        exact hb _⟩
      (fun g' _ => ho g g') β' l'
  have s2 := hS E n μ φ.1 φ.2.1.continuous ⟨C, hb⟩ φ.2.1.isLeftInvariant
    (fun q => starRingEnd ℂ (CuspidalSpectrum.cuspQuot l' q))
    (Complex.continuous_conj.comp (CuspidalSpectrum.continuous_cuspQuot l' hc))
    ⟨D, fun q => by
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [Complex.norm_conj]
      exact hD _⟩
    (fun g _ => by
      have h := congrArg (starRingEnd ℂ) (s1 g)
      rw [← integral_conj, map_zero] at h
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)) h
      simp only [map_mul, Complex.conj_conj]
      exact mul_comm _ _) β l
  have e' : CuspidalSpectrum.cuspQuot l = CuspidalSpectrum.cuspQuot l' :=
    CuspidalSpectrum.cuspQuot_surj_eq l l' fun y => congrFun e _
  rw [e'] at s2
  have z := zero_of_sq μ _ hc D hD l' s2
  rw [e]
  funext x
  obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL x
  exact (conv_left _ _ _ (hφ' s) y).trans (z y hy)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.OrthStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

theorem UpperTheory.V.Af.StrongMultiplicityOne.orthStep :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.OrthStep := by
  classical
  intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n) := by
    set_option synthInstance.maxHeartbeats 400000 in
      infer_instance
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ = ν at *
  have : SFinite ν := sfinite_of_finite ν
  have : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  have : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g) := fun g γ x => by
    show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)
    rw [mul_assoc]
    exact hl γ _
  have hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x := fun x γ g => by
    show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x
    unfold chart
    split_ifs with hx
    · exact hr _ γ g
    · rfl
  let F : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n → ℂ := fun z =>
    CuspidalSpectrum.cuspQuot (hF z.2) z.1
  have hFmk : ∀ (y : Reduction.normOneGL (K := E) (n := n)) x,
      F (RightCosetSpace.mk (Reduction.rationalGLOne (K := E) (n := n)) y, x) = chart f y.1 x := fun _ _ => rfl
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hFb : ∀ z, ‖F z‖ ≤ C := by
    rintro ⟨q, x⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    unfold chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0 := by
    intro q x hx
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    exact dif_neg hx
  have hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)))) ×ˢ invSet E n) :=
    isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet
  have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
    rintro ⟨q, x⟩ ⟨-, hx⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne (K := E) (n := n))).prodMap
      (IsOpenQuotientMap.id (X := Lie E n))
    refine ContinuousAt.continuousWithinAt ?_
    refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
    have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
      (hcc E n f hf).1.continuousAt ((isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
    have h2 : Continuous fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact ContinuousAt.comp (f := fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n))
      (x := (y, x)) h1 h2.continuousAt
  have hFm : Measurable F := by
    have hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ :=
      (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩
    have := hFc.measurable_piecewise hc hopen.measurableSet
    rwa [Set.piecewise_same] at this
  have hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n =>
      (a z.1 * F z) * β z.2)
      (ν.prod volume) := by
    have hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n => β z.2)
        (ν.prod volume) :=
      (β.integrable (μ := volume)).comp_snd _
    refine hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))
  have e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x := by
    intro q
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]
    simp only [hFmk, mul_assoc]
  have e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0 := by
    intro x
    rw [integral_mul_const]
    by_cases hx : x ∈ invSet E n
    · have hx' : IsUnit (Matrix.of x) := hx
      have e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q := by
        intro q
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [hFmk, CuspidalSpectrum.cuspQuot_mk]
        exact dif_pos hx'
      simp only [e]
      rw [h0, zero_mul]
    · simp [hF0 _ x hx]
  simp only [e1]
  rw [integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]
  simp only [e2, integral_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.PsiInf
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.psiInf :
    UpperTheory.V.Af.StrongMultiplicityOne.PsiInf := by
  intro E _ _ _ x
  have h : GroundTheory.Global.adelicChar E (sInf E x) = 𝐞 (-TG.tr E x) := by
    have e : sInf E x = GroundTheory.Global.infiniteAdeleInl (GlobalTheory.CuspRep.infEq E x) := rfl
    rw [e, GroundTheory.Global.adelicChar_infiniteAdeleInl, TG.tr_apply, ← Finset.sum_neg_distrib,
      GroundTheory.Global.addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GroundTheory.Global.infiniteAdelicChar_apply_of_isComplex (IsTotallyComplex.isComplex w)]
    have e2 : InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.CuspRep.infEq E x w) = x w :=
      Cm.mixRing_snd x ⟨w, IsTotallyComplex.isComplex w⟩
    rw [e2]
  exact congrArg (fun z : Circle => (z : ℂ)) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Seed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.Seed := by
  intro hW hS hN E _ _ _ n U hU l sU
  have nice : ∀ φ ∈ U, Nice φ.1 := fun φ hφ => (hN E n φ).2 (l hφ)
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← GlobalTheory.CuspRep.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := sU.τ k φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (finRepCusp E n k φ).1 = fun x => φ.1 (x * finGL E n k) := by
    rw [← Fb.finEmb_eq]
    rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.TrDual
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.trDual :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual := by
  classical
  intro E _ _
  let B : LinearMap.BilinForm ℝ (Cinf E) := (LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)
  have hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0 := fun x h => by
    have h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0 := h fun w => starRingEnd ℂ (x w)
    simp only [Complex.mul_conj, Complex.ofReal_re] at h1
    have b' := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1
    exact funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)
  have hB : B.Nondegenerate := ⟨hl, fun x h => hl x fun y => by
    have := h y
    change TG.tr E (_ * _) = 0 at this ⊢
    rwa [mul_comm]⟩
  let b := Module.finBasis ℝ (Cinf E)
  refine ⟨_, b, B.dualBasis hB b, fun x y => ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rfl
end

