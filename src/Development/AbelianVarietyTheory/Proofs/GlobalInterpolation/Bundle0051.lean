module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0030
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityAndRegions
section
open Complex DirichletCharacter Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZerosNearOne

theorem density_and_regions : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C1 * Q ^ ((1 : ℝ) / 4)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  obtain ⟨c, hc, H2, H3⟩ := GlobalTheory.ZeroFreeHalf.main GlobalTheory.LandauPageRegion.main
  exact ⟨C, c, hC, hc, H, H2, H3⟩

end GlobalTheory.ZerosNearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction
section
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory


open MeasureTheory Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction :
    ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T']
      [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j →
      ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m']
        [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b →
        (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure j m' m ν := by
  intro T T' _ _ _ _ _ _ _ j hj m _ _ m' _ _ _ b hb hint
  refine ⟨(m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j), ?_⟩
  intro f hf
  set F : T → ℝ≥0∞ := fun t => ∫⁻ s, f (j s * t) ∂m' with hFdef
  have hF : Measurable F := by
    have hprod : Measurable fun p : T × T' => f (j p.2 * p.1) :=
      hf.comp ((hj.comp measurable_snd).mul measurable_fst)
    exact hprod.lintegral_prod_right'
  have hG : ∀ t : T,
      ∫⁻ s, f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) ∂m' = F t := by
    intro t
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel j.range) t
    obtain ⟨u, hu⟩ := QuotientGroup.rightRel_apply.mp hrel
    have ht : t = j u * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j) := by
      change t = j u * Quotient.out (Quotient.mk (QuotientGroup.rightRel j.range) t)
      rw [hu, inv_mul_cancel_right]
    simp only [hFdef]
    conv_rhs => rw [ht]
    simp_rw [← mul_assoc, ← map_mul]
    exact (lintegral_mul_right_eq_self
      (fun s => f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j))) u).symm
  set G : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j → ℝ≥0∞ := fun c => ∫⁻ s, f (j s * Quotient.out c) ∂m' with hGdef
  have hGmeas : Measurable G := by
    refine (measurable_from_quotient (s := QuotientGroup.rightRel j.range)).mpr ?_
    convert hF using 1
    funext t
    exact hG t
  have key : ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := by
    calc ∫⁻ t, f t ∂m = ∫⁻ t, (∫⁻ s, b (j s * t) ∂m') * f t ∂m :=
          lintegral_congr fun t => by rw [hint t, one_mul]
      _ = ∫⁻ t, ∫⁻ s, b (j s * t) * f t ∂m' ∂m :=
          lintegral_congr fun t => (lintegral_mul_const _ (hb.comp (hj.mul_const t))).symm
      _ = ∫⁻ s, ∫⁻ t, b (j s * t) * f t ∂m ∂m' :=
          lintegral_lintegral_swap
            ((hb.comp ((hj.comp measurable_snd).mul measurable_fst)).mul
              (hf.comp measurable_fst)).aemeasurable
      _ = ∫⁻ s, ∫⁻ t, b t * f (j s⁻¹ * t) ∂m ∂m' := lintegral_congr fun s => by
          have h := lintegral_mul_left_eq_self (μ := m) (fun t => b t * f (j s⁻¹ * t)) (j s)
          simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h
          exact h
      _ = ∫⁻ t, ∫⁻ s, b t * f (j s⁻¹ * t) ∂m' ∂m :=
          lintegral_lintegral_swap
            ((hb.comp measurable_snd).mul
              (hf.comp ((hj.comp measurable_fst.inv).mul measurable_snd))).aemeasurable
      _ = ∫⁻ t, b t * F t ∂m := lintegral_congr fun t => by
          have hmeas : Measurable fun s : T' => f (j s⁻¹ * t) :=
            hf.comp ((hj.comp measurable_inv).mul_const t)
          rw [lintegral_const_mul _ hmeas]
          congr 1
          exact lintegral_inv_eq_self (fun s => f (j s * t))
  calc ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := key
    _ = ∫⁻ t, b t * G (Quotient.mk'' t) ∂m := lintegral_congr fun t => by rw [← hG t]
    _ = ∫⁻ t, G (Quotient.mk'' t) ∂(m.withDensity b) :=
        (lintegral_withDensity_eq_lintegral_mul _ hb (hGmeas.comp measurable_quotient_mk'')).symm
    _ = ∫⁻ c, G c ∂((m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) :=
        (lintegral_map hGmeas measurable_quotient_mk'').symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.LocalComponentChar


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem index_intV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (LocalAdditiveCharacterDual.intV F v).index = 0 := by
  by_contra hn
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (1 : ℤ))
  have hn' : (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := (LocalAdditiveCharacterDual.intV F v).nsmul_index_mem (t / (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v))
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hn'] at h
  have h1 : Valued.v t ≤ 1 := h
  rw [ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_localChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  intro F _ _ ψ hψ v hfin
  refine ⟨⟨psiV F ψ v, LocalAdditiveCharacterDual.psiV_zero F ψ v, LocalAdditiveCharacterDual.psiV_add F ψ v⟩, ⟨?_, fun t => hψ.2.1 _, ?_⟩,
    fun _ => rfl⟩
  · have h2 : Continuous fun x : Fv F v => pairA F 0 (singleV F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV F v)
    exact hψ.1.comp h2
  · by_contra h
    push Not at h
    have htop : LocalAdditiveCharacterDual.psiDual F ψ v = ⊤ := by
      rw [eq_top_iff]
      intro t _ s _
      exact h _
    apply hfin.1
    rw [htop, AddSubgroup.relIndex_top_right]
    exact index_intV F v

end GlobalTheory.LocalComponentChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdeleCoordinatesCmType
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealAdeleCoord

theorem bijective_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {T : Type} (τ : T → (E →+* ℂ))
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) :
    Function.Bijective fun ρ => InfinitePlace.mk ((τ ρ).comp (algebraMap F E)) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  obtain ⟨δ, h0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  constructor
  · intro i j hij
    apply hτ.1
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' h0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff hij) with e | e
    · simp only [e]
    · simp only [e, InfinitePlace.mk_conjugate_eq]
  · intro w
    obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk (ComplexEmbedding.lift E w.embedding))
    refine ⟨i, ?_⟩
    have := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) hi
    simp only [InfinitePlace.comap_mk, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding] at this
    exact this

theorem exists_realCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ
  haveI hF := h.1
  let u : T ≃ InfinitePlace F := Equiv.ofBijective _ (bijective_place σ h τ hτ)
  let s : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hs : ∀ w, Continuous (s w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hs' : ∀ w, Continuous (s w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hsc : ∀ w x, ((s w x : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w x := fun w x =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) x
  let r : Ainf F ≃+* (T → ℝ) :=
    { toFun := fun a ρ => s (u ρ) (a (u ρ))
      invFun := fun y w => (s w).symm (y (u.symm w))
      left_inv := fun a => funext fun w => by
        obtain ⟨ρ, rfl⟩ := u.surjective w
        show (s (u ρ)).symm (s (u (u.symm (u ρ))) (a (u (u.symm (u ρ))))) = _
        rw [u.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv := fun y => funext fun ρ => by
        show s (u ρ) ((s (u ρ)).symm (y (u.symm (u ρ)))) = _
        rw [RingEquiv.apply_symm_apply, u.symm_apply_apply]
      map_mul' := fun a b => funext fun ρ => map_mul (s (u ρ)) (a (u ρ)) (b (u ρ))
      map_add' := fun a b => funext fun ρ => map_add (s (u ρ)) (a (u ρ)) (b (u ρ)) }
  have hr : ∀ a ρ, r a ρ = s (u ρ) (a (u ρ)) := fun _ _ => rfl
  refine ⟨r, continuous_pi fun ρ => (hs _).comp (continuous_apply (u ρ)),
    continuous_pi fun w => (hs' w).comp (continuous_apply (u.symm w)), fun a ρ => ?_, fun a => ?_, fun a => ?_⟩
  · rw [GlobalTheory.InfAdeleCM.hom_tmul _ _ (hθ ρ).1 (hθ ρ).2, map_one, mul_one, hr, hsc]
    rfl
  · unfold LocalAdditiveCharacterDual.stdInf
    rw [← Complex.exp_sum, ← u.sum_comp]
    congr 1
    simp only [← hsc, ← hr, Complex.ofReal_re]
    push_cast
    rw [← Finset.mul_sum]
    ring
  · constructor
    · intro ha ρ
      rw [hr]
      exact (map_ne_zero _).2 (ha _)
    · intro ha w
      obtain ⟨ρ, rfl⟩ := u.surjective w
      exact (map_ne_zero (s (u ρ))).1 (ha ρ)

end GlobalTheory.RealAdeleCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhat
section
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

theorem exists_unfoldingKernel_levelSubgroup_bruhat : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  intro G G' T T' _ _ _ _ _ _ _ _ _ _ _ μ μ' _ m m' _ K K' hK hK' φ ψ ψ' j hψ hψ' hj hφK hcomm
    hm hm' b hb hb1 f hf hfinv ν hν
  have hbf : Measurable fun t => b t * f t := hb.mul hf
  refine ⟨(K : Set G).indicator (fun h => b (ψ h) * f (ψ h)), (hbf.comp hψ).indicator hK, ?_, ?_⟩
  · rw [lintegral_indicator hK, ← lintegral_map hbf hψ, hm, hν _ hbf]
    refine lintegral_congr fun c => ?_
    simp only [hfinv]
    rw [lintegral_mul_const _ (f := fun s => b (j s * Quotient.out c))
      (hb.comp (hj.mul_const _)), hb1, one_mul]
  · intro h
    by_cases hh : ∃ g, (φ g)⁻¹ * h ∈ K
    · obtain ⟨g₀, hk⟩ := hh
      have hmem : h ∈ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := ⟨g₀, hk⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      obtain ⟨k, rfl⟩ : ∃ k, h = φ g₀ * k := ⟨(φ g₀)⁻¹ * h, by simp⟩
      rw [inv_mul_cancel_left] at hk
      rw [← lintegral_mul_left_eq_self _ g₀]
      have hF : Measurable fun s : T' => b (j s⁻¹ * ψ k) :=
        hb.comp ((hj.comp measurable_inv).mul_const _)
      have key : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h))
          ((φ (g₀ * g))⁻¹ * (φ g₀ * k)) =
          (K' : Set G').indicator (fun g => b (j (ψ' g)⁻¹ * ψ k) * f (ψ k)) g := by
        intro g
        have e : (φ (g₀ * g))⁻¹ * (φ g₀ * k) = (φ g)⁻¹ * k := by
          rw [map_mul]; group
        have e2 : ψ ((φ g)⁻¹ * k) = j (ψ' g)⁻¹ * ψ k := by
          rw [map_mul, map_inv, hcomm, map_inv]
        rw [e]
        by_cases hg : g ∈ K'
        · have : (φ g)⁻¹ * k ∈ (K : Set G) := K.mul_mem (K.inv_mem ((hφK g).2 hg)) hk
          rw [Set.indicator_of_mem this, Set.indicator_of_mem (show g ∈ (K' : Set G') from hg),
            e2, hfinv]
        · have : (φ g)⁻¹ * k ∉ (K : Set G) := fun hx =>
            hg ((hφK g).1 (K.inv_mem_iff.1 ((K.mul_mem_cancel_right hk).1 hx)))
          rw [Set.indicator_of_notMem this,
            Set.indicator_of_notMem (show g ∉ (K' : Set G') from hg)]
      simp only [key]
      rw [lintegral_indicator hK',
        ← lintegral_map (f := fun s : T' => b (j s⁻¹ * ψ k) * f (ψ k)) (hF.mul_const _) hψ', hm',
        lintegral_mul_const _ hF, lintegral_inv_eq_self (fun s => b (j s * ψ k)), hb1, one_mul,
        map_mul, hcomm, hfinv]
    · have hmem : h ∉ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := hh
      rw [Set.indicator_of_notMem hmem, zero_mul]
      have : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h)) ((φ g)⁻¹ * h) = 0 :=
        fun g => Set.indicator_of_notMem (fun hx => hh ⟨g, hx⟩) _
      simp only [this, lintegral_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitarySignatureStabiliserCosetCutoff
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabiliserCutoff

variable {P Q : ℕ}

theorem qf_eq (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.qf x = PerpendicularEmbedding.qf x := by
  have h : ActionCoordinates.herm x x = PerpendicularEmbedding.herm x x := by
    simp [ActionCoordinates.herm, PerpendicularEmbedding.herm, ActionCoordinates.sgn, Fintype.sum_sum_type, sub_eq_add_neg]
  rw [ActionCoordinates.qf, h, PerpendicularEmbedding.herm_self, Complex.ofReal_re]

theorem qf_act (g : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) : PerpendicularEmbedding.qf (ActionCoordinates.act g x) = PerpendicularEmbedding.qf x := by
  have h : (PerpendicularEmbedding.qf (ActionCoordinates.act g x) : ℂ) = PerpendicularEmbedding.qf x := by
    rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self, ActionCoordinates.act, star_mulVec,
      mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      GlobalTheory.UpqTopology.mat_unitary]
  exact_mod_cast h

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem continuous_act (x : ActionCoordinates.Wsp P Q) : Continuous fun g : UpqT P Q => ActionCoordinates.act g x :=
  GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

theorem eq_zero_of_herm {v : ActionCoordinates.Wsp P Q} (h : ∀ w, ActionCoordinates.herm v w = 0) : v = 0 := by
  funext i
  have := h (Pi.single i 1)
  rcases i with i | i <;>
    simpa [ActionCoordinates.herm, ActionCoordinates.sgn, Pi.single_apply, apply_ite] using this

theorem exists_cutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 →
    ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} →
    ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧
      ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  intro c P Q P' Q' x₀ h0 j ι hι hr
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI := c.haar P' Q'
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P' Q' _ (c.haar P' Q')
  obtain ⟨s, hsm, hs⟩ := GlobalTheory.QuadricSection.exists_isSection P Q _ x₀ (qf_eq x₀ ▸ h0) rfl
  obtain ⟨L, hL⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 fun v hv =>
    eq_zero_of_herm fun w => by rw [← hι.1, hv]; simp [ActionCoordinates.herm])
  have hL' : ∀ v, L (j v) = v := fun v => LinearMap.congr_fun hL v
  let Φ : UpqT P' Q' → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun h b => ActionCoordinates.act h (Pi.single b 1)
  let π : UpqT P Q → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun g b => L (ActionCoordinates.act g (j (Pi.single b 1)))
  have hΦ : Continuous Φ := continuous_pi fun b => continuous_act _
  have hπ : Continuous π := continuous_pi fun b =>
    L.continuous_of_finiteDimensional.comp (continuous_act _)
  have hΦi : Function.Injective Φ := fun a b hab =>
    GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective (by
      ext x y
      simpa [Φ, ActionCoordinates.act] using congrFun (congrFun hab y) x)
  have hπι : ∀ a b, π (ι a * ι b) = Φ (a * b) := fun a b => by
    funext x
    simp only [π, Φ, act_mul, (hι.2.2 _).2, hL']
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P' Q')
  have hpos : c.cd P' Q' K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK1).ne'
  have hfin : c.cd P' Q' K ≠ ⊤ := hK.measure_lt_top.ne
  have hO : MeasurableSet (Φ '' K) := (hK.image hΦ).isClosed.measurableSet
  let F : ((Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q') → ℝ≥0∞ :=
    (Φ '' K).indicator fun _ => (c.cd P' Q' K)⁻¹
  have hF : Measurable F := measurable_const.indicator hO
  have hFΦ : ∀ h, F (Φ h) = K.indicator (fun _ => (c.cd P' Q' K)⁻¹) h := fun h => by
    by_cases hh : h ∈ K
    · simp only [F, Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mem_image_of_mem Φ hh)]
    · simp only [F, Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (mt hΦi.mem_set_image.1 hh)]
  refine ⟨fun g => F (π (g * s (ActionCoordinates.act g⁻¹ x₀))), ?_, fun g => ?_⟩
  · exact hF.comp (hπ.measurable.comp (measurable_id.mul
      (hsm.comp ((continuous_act x₀).comp continuous_inv).measurable)))
  · obtain ⟨h₀, hh₀⟩ : g * s (ActionCoordinates.act g⁻¹ x₀) ∈ Set.range ι := by
      rw [hr]
      change ActionCoordinates.act (g * s (ActionCoordinates.act g⁻¹ x₀)) x₀ = x₀
      have e : ActionCoordinates.act (s (ActionCoordinates.act g⁻¹ x₀)) x₀ = ActionCoordinates.act g⁻¹ x₀ := hs _ (qf_act _ _)
      rw [act_mul, e, ← act_mul, mul_inv_cancel, act_one]
    have e : ∀ h, F (π (ι h * g * s (ActionCoordinates.act (ι h * g)⁻¹ x₀))) = F (Φ (h * h₀)) := fun h => by
      have e1 : ActionCoordinates.act (ι h)⁻¹ x₀ = x₀ := by
        conv_lhs => rw [← (hι.2.2 h).1, ← act_mul, inv_mul_cancel, act_one]
      rw [_root_.mul_inv_rev, act_mul, e1, mul_assoc, ← hh₀, hπι]
    simp only [e]
    refine ⟨hF.comp (hΦ.measurable.comp (measurable_mul_const h₀)), ?_⟩
    rw [lintegral_mul_right_eq_self (fun h => F (Φ h)) h₀]
    simp only [hFΦ]
    rw [lintegral_indicator_const hK.isClosed.measurableSet, ENNReal.inv_mul_cancel hpos hfin]

end GlobalTheory.StabiliserCutoff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreMeasureFamilyMapHomeomorph
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory

theorem isFibreFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  intro V V' X X' _ _ _ _ _ _ _ _ _ _ _ _ e r μ ν f f' B fib hf h
  obtain ⟨h1, h2, h3⟩ := h
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hr : MeasurableEmbedding r := r.measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [he.map_apply]
    convert h1 (r.symm b) using 2
    ext v
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.inter_univ, Set.mem_singleton_iff, id, hf]
    exact not_congr r.eq_symm_apply.symm
  · have := h2 (fun v => φ (e v)) (hφ.comp he.measurable)
    rw [Measure.restrict_univ] at this ⊢
    rw [he.lintegral_map, hr.lintegral_map, this]
    refine lintegral_congr fun b => ?_
    rw [he.lintegral_map, r.symm_apply_apply]
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [he.integrable_map_iff, r.symm_apply_apply]
      exact h4 b hb
    · have h6 := h5.comp (s := r '' B) r.symm.continuous.continuousOn (by
        rintro _ ⟨b, hb, rfl⟩
        rw [r.symm_apply_apply]
        exact hb)
      refine h6.congr fun b _ => ?_
      simp only [Function.comp]
      rw [he.integral_map]

end GlobalTheory
end

