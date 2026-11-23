module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharTrivialUniformizers
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.HeckeUnifApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inf

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def swapL : (InfiniteAdeleRing F ⊗[F] E) →ₗ[InfiniteAdeleRing F] (E ⊗[F] InfiniteAdeleRing F) where
  toFun := Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

def swapR : (E ⊗[F] InfiniteAdeleRing F) →ₗ[InfiniteAdeleRing F] (InfiniteAdeleRing F ⊗[F] E) where
  toFun := Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

theorem exists_infinite_equiv :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  letI tB : TopologicalSpace (E ⊗[F] InfiniteAdeleRing F) := moduleTopology (InfiniteAdeleRing F) _
  haveI : IsModuleTopology (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F) := ⟨rfl⟩
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have hL : Continuous (swapL (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  have hR : Continuous (swapR (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  let h := GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph (K := F) (L := E)
  refine ⟨(Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E).toRingEquiv.trans
    (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)).toRingEquiv, ?_, ?_, ?_⟩
  · exact h.continuous.comp hL
  · exact hR.comp h.symm.continuous
  · intro x
    change GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x)) = _
    rw [Algebra.TensorProduct.comm_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one,
      mul_one]

end Inf


open GlobalTheory.LFun in
theorem exists_tensor_adele_equiv :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv (F := F) (E := E)
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc,
    hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩


open GlobalTheory.LFun in
theorem exists_hchar (χ : (AF F ⊗[F] E)ˣ →* Circle) (hχ : IsHecke F E χ) :
    ∃ (H : Formalism.L2.Host.HChar E) (u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ),
      (∀ y, H.1 y = Circle.toUnits (χ (u y))) ∧ Function.Surjective u ∧
      ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x := by
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv (F := F) (E := E)
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, u, fun y => rfl, fun g => ⟨Units.map Φ.toRingHom.toMonoidHom g, Units.ext (Φ.symm_apply_apply _)⟩,
    fun W x => ?_⟩
  change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
  rw [hloc]

theorem eq_one_of_unif_cofinite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), GlobalTheory.LFun.IsHecke F E χ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ → χ (GlobalTheory.LFun.locIdele F w ϖ) = 1) → χ = 1 := by
  intro F E _ _ _ _ _ χ hχ hev
  obtain ⟨H, u, hH, hsurj, hloc⟩ := exists_hchar χ hχ
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ →
      χ (GlobalTheory.LFun.locIdele F w ϖ) = 1}.Finite := Filter.eventually_cofinite.1 hev
  have h1 : H.1 = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away H.1 H.2.1 H.2.2 hfin.toFinset fun v hv x => ?_
    have hv' : ∀ ϖ, Formalism.L2.Host.IsUnifAt v ϖ → χ (GlobalTheory.LFun.locIdele F v ϖ) = 1 := by
      simpa using hv
    refine GlobalTheory.FrobDense.eq_one_of_unif (H.1.comp (Neutral.B1.localIdele E v)) (fun y hy => ?_) x
    change H.loc v y = 1
    rw [hloc, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, hv' y hy, map_one]
  ext g
  obtain ⟨y, rfl⟩ := hsurj g
  have h2 : Circle.toUnits (χ (u y)) = 1 := (hH y).symm.trans (congrFun (congrArg DFunLike.coe h1) y)
  have h3 : ((χ (u y) : Circle) : ℂ) = 1 := by
    have := congrArg (fun z : ℂˣ => (z : ℂ)) h2
    simpa using this
  simpa using h3

end GlobalTheory.HeckeUnifApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaSobolevBase

open scoped Classical SchwartzMap ENNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_invOf_two [Invertible (2 : AF F)] :
    evHom F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h2 : evHom F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evHom F) 2, ← map_mul, invOf_mul_self, map_one]
  calc evHom F (⅟(2 : AF F)) = evHom F (⅟(2 : AF F)) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (2 * (1 / 2)) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
    _ = (evHom F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
        rw [map_mul, map_ofNat]; ring
    _ = _ := by rw [h2, one_mul]

def sumPure {ι : Type} [Fintype ι] (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) : (κ → AF F) → ℂ :=
  ∑ i, pureA F (f i) (g i)

theorem exists_sumPure {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (n : ℕ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin n → SInf F κ), (∀ i, g i ∈ SB _) ∧
      Φ = sumPure g f := by
  obtain ⟨n, c, p, hp⟩ := Submodule.mem_span_set'.1 hΦ
  choose f g hg he using fun i => (p i).2
  refine ⟨n, g, fun i => c i • f i, hg, ?_⟩
  rw [← hp, sumPure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i, ← GlobalTheory.WeilAdm.pureA_smul]
  rfl

theorem memLp_pureA (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB _) :
    MemLp (pureA F f g) 2 μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨ν, hν, C, c, hC, -, -, h, -⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg ⊤ isOpen_univ
  have hc : Continuous (pureA F f g) := by
    have h1 := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ (pureA F f g)
      (Submodule.subset_span ⟨f, g, hg, rfl⟩)
    have h2 := h1.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
    convert h2 using 1
    funext x
    simp
  have hf : ∫⁻ z, ‖f z‖ₑ ^ 2 < ⊤ := by
    have := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) (f.memLp 2 volume)
    simpa using this
  have hν2 : MemLp (pureA F f g) 2 ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num) hc.aestronglyMeasurable]
    have := (h f).trans_lt (ENNReal.mul_lt_top hC.lt_top hf)
    simpa using this
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  exact hν2.smul_measure ENNReal.coe_ne_top

end GlobalTheory.ThetaSobolevBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

theorem isUnit_of_sub_mem_maximalIdeal' {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (h : x - y ∈ maximalIdeal A) (hy : IsUnit y) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have hy' : y ∈ maximalIdeal A := by
    have := Ideal.sub_mem _ hx' h
    simpa using this
  exact (mem_maximalIdeal y).1 hy' hy

theorem eq_of_isRoot_of_sub_mem_maximalIdeal {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {f : A[X]} {a₀ b b' : A} (hu : IsUnit (f.derivative.eval a₀)) (hb : f.IsRoot b) (hb' : f.IsRoot b')
    (h1 : b - a₀ ∈ maximalIdeal A) (h2 : b' - a₀ ∈ maximalIdeal A) : b' = b := by
  set h := f /ₘ (X - C b) with hh
  have hf : f = (X - C b) * h := (mul_divByMonic_eq_iff_isRoot.2 hb).symm
  have hd : f.derivative.eval b = h.eval b := by
    rw [hf]
    simp [derivative_mul]
  have hub : IsUnit (h.eval b) := by
    rw [← hd]
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hu
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b a₀ f.derivative
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  have hub' : IsUnit (h.eval b') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hub
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b' b h
    rw [hc]
    apply Ideal.mul_mem_right
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  have e : (b' - b) * h.eval b' = 0 := by
    have := hb'
    rw [IsRoot, hf] at this
    simpa using this
  rcases mul_eq_zero.1 e with e | e
  · exact sub_eq_zero.1 e
  · exact absurd e hub'.ne_zero

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_of_isSepClosed {Ω : Type} [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing V := by
  classical
  obtain ⟨W, rfl⟩ := exists_valuationSubring_comap_eq V (algebraMap Ω (AlgebraicClosure Ω))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  set ψ := comapToValuationSubring W (algebraMap Ω (AlgebraicClosure Ω))
  set ιW := algebraMap W (AlgebraicClosure Ω)
  set G := f.map ψ with hG
  set F := G.map ιW with hF
  have hFm : F.Monic := (hf.map ψ).map ιW
  have hint : ∀ r ∈ F.roots, ∃ r' : W, ιW r' = r := by
    intro r hr
    have hi : IsIntegral W r := ⟨G, hf.map ψ, by
      rw [← Polynomial.eval_map]
      exact (mem_roots hFm.ne_zero).1 hr⟩
    exact IsIntegrallyClosed.isIntegral_iff.1 hi
  have hψm : ψ (f.eval a₀) ∈ maximalIdeal W :=
    (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map ψ _ hu)

  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, W.valuation (ιW (ψ a₀) - r) < 1 := by
    by_contra hne
    push_neg at hne
    have hprod : F.eval (ιW (ψ a₀)) = (F.roots.map fun r => ιW (ψ a₀) - r).prod := by
      conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
        IsAlgClosed.card_roots_eq_natDegree]
      rw [eval_multiset_prod, Multiset.map_map]
      simp
    have h1 : W.valuation (F.eval (ιW (ψ a₀))) = 1 := by
      rw [hprod, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hle := hne y hy
      obtain ⟨y', rfl⟩ := hint y hy
      refine le_antisymm ?_ hle
      simp only [Function.comp_apply]
      rw [← map_sub]
      exact W.valuation_le_one (ψ a₀ - y')
    have h2 : W.valuation (F.eval (ιW (ψ a₀))) < 1 := by
      rw [hF, Polynomial.eval_map, eval₂_at_apply, hG, Polynomial.eval_map, eval₂_at_apply]
      exact (W.valuation_lt_one_iff _).1 hψm
    exact absurd h1 h2.ne
  obtain ⟨r', rfl⟩ := hint r hr
  have hr'm : r' - ψ a₀ ∈ maximalIdeal W := by
    rw [← neg_sub, Ideal.neg_mem_iff, W.valuation_lt_one_iff]
    simpa [ιW] using hrv
  have hGd : IsUnit (G.derivative.eval r') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ (y := G.derivative.eval (ψ a₀)) ?_
    · obtain ⟨c, hc⟩ := sub_dvd_eval_sub r' (ψ a₀) G.derivative
      rw [hc]
      exact Ideal.mul_mem_right _ _ hr'm
    · rw [hG, derivative_map, Polynomial.eval_map, eval₂_at_apply]
      exact h₂.map ψ
  have hFd : F.derivative.eval (ιW r') ≠ 0 := by
    rw [hF, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact fun e => hGd.ne_zero ((injective_iff_map_eq_zero ιW).1 (FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)) _ e)
  have hιinj : Function.Injective ιW := FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)
  have hψinj : Function.Injective ψ := fun x y e =>
    Subtype.ext ((algebraMap Ω (AlgebraicClosure Ω)).injective (congrArg Subtype.val e))

  set F₀ : Polynomial Ω := f.map (W.comap (algebraMap Ω (AlgebraicClosure Ω))).subtype with hF₀
  have hF₀F : F₀.map (algebraMap Ω (AlgebraicClosure Ω)) = F := by
    rw [hF₀, hF, hG, Polynomial.map_map, Polynomial.map_map]
    rfl
  have hintΩ : IsIntegral Ω (ιW r') := Algebra.IsIntegral.isIntegral _
  have hroot0 : aeval (ιW r') F₀ = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, hF₀F]
    exact (mem_roots hFm.ne_zero).1 hr
  obtain ⟨h, hh⟩ := minpoly.dvd Ω (ιW r') hroot0
  have hq : aeval (ιW r') (derivative (minpoly Ω (ιW r'))) ≠ 0 := by
    intro e
    apply hFd
    have : aeval (ιW r') (derivative F₀) = 0 := by
      rw [hh, derivative_mul, map_add (f := _), map_mul, map_mul, e, minpoly.aeval]
      ring
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF₀F] at this
    exact this
  have hsep : (minpoly Ω (ιW r')).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hintΩ)).2 (fun e => hq (by rw [e, map_zero]))
  have hdeg := IsSepClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hintΩ) hsep
  obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.1 (natDegree_eq_of_degree_eq_some hdeg)
  have hbW : b ∈ W.comap (algebraMap Ω (AlgebraicClosure Ω)) := by
    rw [ValuationSubring.mem_comap, hb]
    exact r'.2
  have hψb : ψ ⟨b, hbW⟩ = r' := Subtype.ext hb
  have hGr : G.eval r' = 0 := by
    apply hιinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← hF]
    exact (mem_roots hFm.ne_zero).1 hr
  refine ⟨⟨b, hbW⟩, ?_, ?_⟩
  · apply hψinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hψb, ← hG]
    exact hGr
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hr'm ?_
    have := hu.map ψ
    rwa [map_sub, hψb] at this

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_comap_fixedField_inertia (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  classical
  haveI := henselianLocalRing_of_isSepClosed V
  set K' := IntermediateField.fixedField (inertia K V)
  set j := comapToValuationSubring V (algebraMap K' Ω)
  have hjinj : Function.Injective j := fun x y e =>
    Subtype.ext ((algebraMap K' Ω).injective (congrArg (fun z : V => (z : Ω)) e))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  have h₁' : (f.map j).eval (j a₀) ∈ maximalIdeal V := by
    rw [Polynomial.eval_map, eval₂_at_apply]
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map j _ hu)
  have h₂' : IsUnit ((f.map j).derivative.eval (j a₀)) := by
    rw [derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact h₂.map j
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian (f.map j) (hf.map j) (j a₀) h₁' h₂'

  set κ : V.comap (algebraMap K' Ω) →+* Ω := V.subtype.comp j with hκ
  have hbΩ : f.eval₂ κ (b : Ω) = 0 := by
    have : V.subtype ((f.map j).eval b) = 0 := by rw [hb.eq_zero, map_zero]
    rw [Polynomial.eval_map, hom_eval₂] at this
    exact this
  have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
    intro σ hσ
    obtain ⟨hσV, hσv⟩ := (mem_inertia_iff V σ).1 hσ
    have hmem : σ (b : Ω) ∈ V := by
      have := ValuationSubring.smul_mem_pointwise_smul σ (b : Ω) V b.2
      rwa [hσV] at this
    have hσκ : (σ : Ω →+* Ω).comp κ = κ := by
      ext x
      exact (IntermediateField.mem_fixedField_iff _ _).1 (x : K').2 σ hσ
    have hc : (f.map j).IsRoot ⟨σ b, hmem⟩ := by
      apply V.subtype_injective
      rw [map_zero, Polynomial.eval_map, hom_eval₂]
      have e := congrArg (σ : Ω →+* Ω) hbΩ
      rw [map_zero, hom_eval₂, hσκ] at e
      exact e
    have hcm : (⟨σ b, hmem⟩ : V) - j a₀ ∈ maximalIdeal V := by
      have hd : (⟨σ b, hmem⟩ : V) - b ∈ maximalIdeal V := by
        rw [V.valuation_lt_one_iff]
        exact hσv b b.2
      have := Ideal.add_mem _ hd hba
      simpa using this
    have := eq_of_isRoot_of_sub_mem_maximalIdeal h₂' hb hc hba hcm
    exact congrArg Subtype.val this
  have hbK : (b : Ω) ∈ K' := (IntermediateField.mem_fixedField_iff _ _).2 hfix
  have hbV : (⟨b, hbK⟩ : K') ∈ V.comap (algebraMap K' Ω) := b.2
  have hjb : j ⟨⟨b, hbK⟩, hbV⟩ = b := Subtype.ext rfl
  refine ⟨⟨⟨b, hbK⟩, hbV⟩, ?_, ?_⟩
  · apply hjinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hjb]
    exact hb
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hba ?_
    have := hu.map j
    rwa [map_sub, hjb] at this

theorem henselianLocalRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact henselianLocalRing_comap_fixedField_inertia K V

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem inertia_conj_mem_smul : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  intro K Ω _ _ _ V g σ hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ

  have hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1 := by
    intro z hz
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
    rcases hz with hz | hz
    · left; simp [hz]
    · right
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      intro h
      apply hz
      have : (g⁻¹ • (g z)⁻¹) = z⁻¹ := by
        change g⁻¹ ((g z)⁻¹) = z⁻¹
        rw [map_inv₀]
        simp
      rwa [this] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    set y := g⁻¹ • x with hy
    have hxy : x = g y := by simp [hy]
    have : (g * σ * g⁻¹) x - x = g (σ y - y) := by
      rw [map_sub, hxy]
      simp
    rw [this]
    exact hn _ (h2 y hx)

end GlobalTheory
end

