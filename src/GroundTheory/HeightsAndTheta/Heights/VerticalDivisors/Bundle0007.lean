module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem gaussNormOf_rename {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _

theorem specFirst_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]

theorem gaussNorm_map_eq_one {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem GaussEq.proof (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem NormFormLocalization.proof : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, map_X, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem specComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1

theorem vertComps_finite' {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1


open Classical in
theorem OrdEq.proof (hni : NormIdentity.Statement) (hnl : NormLength.Statement)
    (hld : LengthDecomp.Statement) (hmax : SpecMax.Statement) (hlen : SpecLength.Statement)
    (hres : SpecResidue.Statement) (hvs : VertSpec.Statement) (hinj : SecBLinInj.Statement)
    (hfin : SecBFinite.Statement) (htf : SecBTorsionFree.Statement) (hdvr : ParDVRIsDVR.Statement) :
    OrdEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  set f := g.map (algebraMap (𝓞 K) K)
  set ℓ := secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))
  obtain ⟨w, hw⟩ := hni K n e I g u v hI hf hu hprim
  rw [hw, Ring.ord_mul_of_isUnit_left w.isUnit]
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I f v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  have hℓ : Function.Injective fun b : SecB e I v => ℓ * b := hinj K n e I f u v hI hf hu
  rw [hnl _ _ ℓ hℓ]

  have hN0 : Algebra.norm (ParDVR e n v) ℓ ≠ 0 := by
    rw [Algebra.norm_apply, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hℓ
  have hfinite : Module.length (ParDVR e n v) (SecB e I v ⧸ Ideal.span {ℓ}) ≠ ⊤ := by
    rw [← hnl _ _ ℓ hℓ]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hN0)
  rw [hld _ _ ℓ hfinite]

  obtain ⟨hmax1, hmax2⟩ := hmax K n e I f v hI hf
  choose W hW hWu using fun 𝔫 : MaximalSpectrum (SecB e I v) => hmax2 𝔫.asIdeal 𝔫.isMaximal
  set G : Ideal (MvPolynomial (Fin n) (𝓞 K)) → ℕ∞ := fun W =>
    (if linForm u ∈ W then (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0) *
      (chowDegree (reduceMod v W) (e + 1) : ℕ∞) with hG
  have hbij : Set.BijOn W Set.univ (specComps I v) := by
    refine ⟨fun 𝔫 _ => (hW 𝔫).1, fun 𝔫₁ _ 𝔫₂ _ h => ?_, fun W' hW' => ?_⟩
    · apply MaximalSpectrum.ext
      rw [← (hW 𝔫₁).2, ← (hW 𝔫₂).2, h]
    · refine ⟨⟨secIdealOf e I v W', hmax1 W' hW'⟩, Set.mem_univ _, ?_⟩
      exact (hWu _ W' ⟨hW', rfl⟩).symm
  rw [← finsum_mem_univ, finsum_mem_eq_of_bijOn W hbij (g := G) fun 𝔫 _ => by
    rw [hlen K n e I f u v hI hf hu 𝔫 (W 𝔫) (hW 𝔫).1 (hW 𝔫).2, ← (hW 𝔫).2,
      hres K n e I f v hI hf (W 𝔫) (hW 𝔫).1]]

  have hs := specComps_finite I v
  have hv := vertComps_finite' I u v
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, vertDeg, Nat.cast_finsum_mem hv,
    finsum_mem_eq_finite_toFinset_sum _ hv]
  have hset : hv.toFinset = hs.toFinset.filter fun W => linForm u ∈ W := by
    ext W
    simp [hvs K n e I f u v hI hf hu]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [hG]
  split_ifs <;> simp

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

theorem PrimitiveScale.proof : PrimitiveScale.Statement := by
  intro K _ _ v σ f hf
  classical
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m)
    with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, FractionalIdeal.spanFinset_ne_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  have hcoeff : ∀ m, f.coeff m ∈ J := by
    intro m
    by_cases hm : f.coeff m = 0
    · rw [hm, ← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _
    · rw [← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]
      exact Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m := by
    intro c hc m
    have h1 : f.coeff m * c ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul (hcoeff m) hc
    rw [hJJ, FractionalIdeal.mem_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [hy, mul_comm]⟩

  have hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal := by
    by_contra hne
    push Not at hne
    let S : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal
    have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro j hj c hc
      have hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c) := by
        rw [hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]
        rintro _ ⟨m, -, rfl⟩
        obtain ⟨y, hy⟩ := hint c hc m
        refine Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩
        simp only [Algebra.linearMap_apply, LinearMap.mulRight_apply]
        rw [hy, mul_comm]
      exact hJS hj
    have h1 : (1 : K) ∈ S := by
      apply hle
      rw [hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    obtain ⟨y, hy, hy1⟩ := Submodule.mem_map.mp h1
    have : y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      simpa using hy1
    rw [this] at hy
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)
  obtain ⟨c, hc, m0, y0, hy0, hy0v⟩ := hex
  have hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K) := by
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    obtain ⟨y, hy⟩ := hint c hc m
    exact ⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩
  obtain ⟨g, hg⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0v
    have : algebraMap (𝓞 K) K y0 = 0 := by rw [hy0, zero_mul]
    rw [(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨c, g, hc0, hg, m0, ?_⟩
  have hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0 := by
    rw [hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]
  rwa [(IsFractionRing.injective (𝓞 K) K) hgm]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem parToFrac_algebraMap {K : Type*} [Field K] [NumberField K] (e n : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) x) = kToFrac K e n (algebraMap (𝓞 K) K x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem map_secLin {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secLin, linForm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j) := rfl
  have h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j)) :=
    rfl
  rw [h1, h2, hr]
  exact congrArg _ (hc j)

theorem SecBLinInj.proof (h1 : SecBGeneric.Statement) (h2 : SecBTorsionFree.Statement)
    (h3 : SecLinNZD.Statement) (h4 : ParAlgIndep.Statement) : SecBLinInj.Statement := by
  intro K _ _ n e I f u v hI hf hu
  obtain ⟨φ, hφc, hφr, hloc⟩ := h1 K n e I v hI
  let _ : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨m, hm⟩, hmb⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
      (SecAlg (idealF e I) (parYF K e n)) b).mp hb
    obtain ⟨r, hr, rfl⟩ := hm
    exact h2 K n e I v hI r b (nonZeroDivisors.ne_zero hr) ((Algebra.smul_def r b).trans hmb)
  let _ := (kToFrac K e n).toAlgebra
  have hnzd := h3 K (ParFrac K e n) n e I f (parYF K e n) (fun j => (u j : K)) (h4 K e n) hI hf hu
  have hmap : φ (secLin (modelR e I v) (parY e n v) fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      secLin (idealF e I) (parYF K e n) (fun j => kToFrac K e n (u j : K)) := by
    rw [map_secLin φ (parToFrac e n v) hφc hφr]
    simp only [parToFrac_algebraMap]
  intro b c hbc
  apply hφinj
  have h := congrArg φ hbc
  simp only [map_mul, hmap] at h
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp h

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem vertComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

theorem VertTermEq.proof : VertTermEq.Statement := by
  intro K _ _ n e I u v
  have hfin := vertComps_finite I u v
  unfold vertTermAt vertDeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun W _ => ?_
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

