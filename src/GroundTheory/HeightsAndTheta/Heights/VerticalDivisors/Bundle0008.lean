module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecBGeneric

variable {K : Type*} [Field K] [NumberField K]

theorem parToFrac_comp_algebraMap (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (parToFrac e n v).comp (algebraMap (𝓞 K) (ParDVR e n v)) =
      (kToFrac K e n).comp (algebraMap (𝓞 K) K) := by
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem parToFrac_parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by
  rw [parY, parToFrac, IsLocalization.lift_eq, parYF]

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]

theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl) fun f hf => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) f.coeffs
  have hb0 : (algebraMap (𝓞 K) K b) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  have hrange : C (algebraMap (𝓞 K) K b) * f ∈ Set.range (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    by_cases h0 : AddMonoidAlgebra.coeff f m = 0
    · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
    · obtain ⟨y, hy⟩ := hb _ (coeff_mem_coeffs m h0)
      exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  obtain ⟨g, hg⟩ := hrange
  have hgI : g ∈ integralModel I := by
    show MvPolynomial.map (algebraMap (𝓞 K) K) g ∈ I
    rw [hg]
    exact I.mul_mem_left _ hf
  have : f = C (algebraMap (𝓞 K) K b)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) g := by
    rw [hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgI)

theorem map_secIdeal {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (secIdeal (modelR e I v) (parY e n v)).map (MvPolynomial.map (parToFrac e n v)) =
      secIdeal (idealF e I) (parYF K e n) := by
  have h1 : (modelR e I v).map (MvPolynomial.map (parToFrac e n v)) = idealF e I := by
    have hc : (MvPolynomial.map (parToFrac e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) : MvPolynomial (Fin n) (𝓞 K) →+* _) =
        (MvPolynomial.map (kToFrac K e n)).comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply, MvPolynomial.map_map, parToFrac_comp_algebraMap]
    rw [modelR, Ideal.map_map, hc, ← Ideal.map_map, map_integralModel, idealF]
  have h2 : (Ideal.span (Set.range (secForm (parY e n v)))).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span (Set.range (secForm (parYF K e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [secForm, map_linForm, parToFrac_parY]
  have h3 : (Ideal.span {chartForm (parY e n v) - 1}).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span {chartForm (parYF K e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    simp only [parToFrac_parY]
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]

end SecBGeneric


open SecBGeneric in
theorem SecBGeneric.proof : SecBGeneric.Statement := by
  intro K _ _ n e I v _
  have hJ := map_secIdeal e I v
  let M : Submonoid (MvPolynomial (Fin n) (ParDVR e n v)) :=
    (nonZeroDivisors (ParDVR e n v)).map (MvPolynomial.C : ParDVR e n v →+* MvPolynomial (Fin n) (ParDVR e n v))
  let φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n) :=
    Ideal.quotientMap _ (MvPolynomial.map (parToFrac e n v)) (hJ ▸ Ideal.le_comap_map)
  refine ⟨φ, fun j => ?_, fun r => ?_, ?_⟩
  · simp [φ, secCoord, Ideal.quotientMap_mk]
  · have hr : algebraMap (ParDVR e n v) (SecB e I v) r =
        Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (C r) := rfl
    rw [hr]
    simp only [φ, Ideal.quotientMap_mk, map_C]
    rfl
  let := φ.toAlgebra
  let : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsFractionRing (ParDVR e n v) (ParFrac K e n) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl _ _
  let : Algebra (MvPolynomial (Fin n) (ParDVR e n v)) (MvPolynomial (Fin n) (ParFrac K e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (ParDVR e n v)) (ParFrac K e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (ParFrac K e n)) (S' := SecAlg (idealF e I) (parYF K e n))
    (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (idealF e I) (parYF K e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  have hM : Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)) =
      M.map (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) := by
    ext x
    simp only [M, Algebra.algebraMapSubmonoid, Submonoid.mem_map, exists_exists_and_eq_and]
    exact Iff.rfl
  rw [hM]
  exact key

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecLinNZD
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem eval_specRest {k E : Type*} [CommRing k] [CommRing E] (φ : k →+* E) {n e : ℕ}
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (u : Fin n → k) :
    eval (fun j => φ (u j)) (specRest φ g y) =
      eval₂ φ (fun ij : Fin e × Fin n => y (.inl ij)) (specFirst g u) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [specRest, specFirst]
  | add p q hp hq =>
    simp only [specRest, specFirst, eval₂_add, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ij hp =>
    simp only [specRest, specFirst, eval₂_mul, eval₂_X, map_mul, bind₁_X_right] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [specFirstVar]

theorem SecLinNZD.proof (h1 : ChowNormForm.Statement) (h2 : NormFormEval.Statement)
    (h3 : SpecFirstNeField.Statement) : SecLinNZD.Statement := by
  intro k E _ _ _ _ n e Q g y u hy hQ hg hu
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  obtain ⟨hfin, c, _, hcg⟩ := h1 k E n e Q g y hy hQ hg
  have hy' : AlgebraicIndependent k (fun ij : Fin e × Fin n => y (.inl ij)) :=
    hy.comp _ Sum.inl_injective
  have hne : eval (fun j => algebraMap k E (u j)) (specRest (algebraMap k E) g y) ≠ 0 := by
    rw [eval_specRest]
    exact fun h0 => h3 k n e Q g u hQ hg hu
      (hy'.eq_zero_of_aeval_eq_zero _ (by rw [aeval_def]; exact h0))
  have hsum : (∑ j, algebraMap E (SecAlg QE y) (algebraMap k E (u j)) * secCoord QE y j) =
      secLin QE y (fun j => algebraMap k E (u j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [secLin, linForm, map_sum, map_mul]
    rfl
  have hnorm : Algebra.norm E (secLin QE y (fun j => algebraMap k E (u j))) ≠ 0 := by
    have h := h2 E (SecAlg QE y) n (secCoord QE y) (fun j => algebraMap k E (u j))
    rw [hsum] at h
    rw [hcg, eval_mul, eval_C, h] at hne
    exact right_ne_zero_of_mul hne
  have hunit : IsUnit (Algebra.lmul E (SecAlg QE y) (secLin QE y fun j => algebraMap k E (u j))) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hnorm
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp hunit).2 1
  have hz' : secLin QE y (fun j => algebraMap k E (u j)) * z = 1 := by
    simpa using hz
  exact (isUnit_iff_exists_inv.mpr ⟨z, hz'⟩).mem_nonZeroDivisors

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertSpec
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem not_lt_lt_of_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] [hW : W.IsPrime] {x : A}
    (hmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q < W) : False := by
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have prime_map : ∀ J : Ideal A, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime :=
    fun J _ hPJ => Ideal.map_isPrime_of_surjective hsurj (hker.trans_le hPJ)
  have strict : ∀ J₁ J₂ : Ideal A, P ≤ J₁ → J₁ < J₂ →
      J₁.map (Ideal.Quotient.mk P) < J₂.map (Ideal.Quotient.mk P) := by
    intro J₁ J₂ h₁ h₁₂
    refine lt_of_le_of_ne (Ideal.map_mono h₁₂.le) fun h => h₁₂.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hsurj, Ideal.comap_map_of_surjective' _ hsurj, hker,
      sup_eq_left.mpr h₁, sup_eq_left.mpr (h₁.trans h₁₂.le)] at this
  have := prime_map P hP le_rfl
  have := prime_map Q hQ hPQ.le
  have := prime_map W hW (hPQ.le.trans hQW.le)
  have a := Ideal.height_add_one_le_of_lt_of_isPrime (strict P Q le_rfl hPQ)
  have b := Ideal.height_add_one_le_of_lt_of_isPrime (strict Q W hPQ.le hQW)
  have : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (P.map (Ideal.Quotient.mk P)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ (W.map (Ideal.Quotient.mk P)).height := b
      _ ≤ 1 := h1
  exact absurd this (by norm_num)

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_zero_of_C_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsPrime)
    {c : 𝓞 K} (hc : C c ∈ integralModel I) : c = 0 := by
  by_contra h
  apply hI.ne_top
  simp only [integralModel, Ideal.mem_comap, map_C] at hc
  have hu : IsUnit (C (algebraMap (𝓞 K) K c) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr h)).map C
  exact Ideal.eq_top_of_isUnit_mem _ hc hu

theorem linForm_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} {u : Fin n → 𝓞 K}
    (h : linForm u ∈ integralModel I) : linForm (fun j => (u j : K)) ∈ I := by
  simp only [integralModel, Ideal.mem_comap] at h
  convert h using 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum, map_mul, map_C, map_X]

theorem VertSpec.proof : VertSpec.Statement := by
  intro K _ _ n e I f u v hI _ hu
  have : I.IsPrime := hI.isPrime
  have hP : (integralModel I).IsPrime := by unfold integralModel; infer_instance
  have hl : linForm u ∉ integralModel I := fun h => hu (linForm_mem_integralModel h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hCa : C a ∉ integralModel I := fun h => ha0 (eq_zero_of_C_mem_integralModel hI.isPrime h)
  ext W
  constructor
  · rintro ⟨⟨hWmin, hWrel⟩, hWv⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := Ideal.map_le_iff_le_comap.mpr hWv.ge
    refine ⟨⟨⟨⟨inferInstance, sup_le (le_sup_left.trans hWmin.1.2) hvW⟩, fun Q hQ hQW => ?_⟩,
      hWrel⟩, hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hCa (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem C ha)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWmin hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)
  · rintro ⟨⟨hWmin, hWrel⟩, hlW⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := le_sup_right.trans hWmin.1.2
    have hPW : integralModel I ≤ W := le_sup_left.trans hWmin.1.2
    have hcomap : W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal :=
      (v.isMaximal.eq_of_le (Ideal.IsPrime.comap C).ne_top
        (Ideal.map_le_iff_le_comap.mp hvW)).symm
    have hWa : W ∈ (integralModel I ⊔ Ideal.span {C a}).minimalPrimes := by
      refine ⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr
        (Set.singleton_subset_iff.mpr (hvW (Ideal.mem_map_of_mem C ha))))⟩, fun Q hQ hQW => ?_⟩
      have := hQ.1
      have hQv : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal := by
        have hle : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≤ v.asIdeal :=
          hcomap ▸ Ideal.comap_mono hQW
        have hmem : a ∈ Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) :=
          hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        have hne : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≠ ⊥ := fun h =>
          ha0 (by rwa [h, Ideal.mem_bot] at hmem)
        exact (Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap C) hne).eq_of_le
          v.isPrime.ne_top hle
      exact hWmin.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
        (Ideal.map_le_iff_le_comap.mpr hQv.ge)⟩ hQW
    refine ⟨⟨⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hlW))⟩,
      fun Q hQ hQW => ?_⟩, hWrel⟩, hcomap⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hl (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWa hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

section Generic

variable (k : Type*) [Field k] (e n : ℕ)

abbrev GenParField : Type _ := FractionRing (MvPolynomial (Par e n) k)

def genPar : Par e n → GenParField k e n :=
  fun p => algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)

abbrev GenSec {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k)) : Type _ :=
  SecAlg (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)

end Generic

def ChowNormFormGeneric.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite (GenParField k e n) (GenSec k e Q) ∧
        ∃ c : GenParField k e n, c ≠ 0 ∧
          specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
            C c * normForm (GenSec k e Q)
              (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))

def SecAlgFieldChange.Statement : Prop :=
  ∀ (E₀ E : Type) [Field E₀] [Field E] (φ : E₀ →+* E) (n e : ℕ)
    (Q₀ : Ideal (MvPolynomial (Fin n) E₀)) (y₀ : Par e n → E₀), Module.Finite E₀ (SecAlg Q₀ y₀) →
      Module.Finite E (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀)) ∧
        (normForm (SecAlg Q₀ y₀) (secCoord Q₀ y₀)).map φ =
          normForm (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))
            (secCoord (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))

def SecAlgFinite.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

def GenSecDomain.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsDomain (GenSec k e Q)

def GenSecSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Algebra.IsSeparable (GenParField k e n) (GenSec k e Q)

def ChowSecDvd.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∃ m : ℕ, 0 < m ∧
        (∑ j, X j * C (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y j)) ∣
          ((specRest (algebraMap k E) g y).map
            (algebraMap E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y))) ^ m

def NormFormIrreducible.Statement : Prop :=
  ∀ (E L : Type) [Field E] [CommRing L] [IsDomain L] [Algebra E L] [Module.Finite E L]
    [Algebra.IsSeparable E L] (n : ℕ) (x : Fin n → L) (t : Fin n → E),
    Algebra.adjoin E (Set.range x) = ⊤ → ∑ j, algebraMap E L (t j) * x j = 1 →
      Irreducible (normForm (R := E) L x)

def GenChowIrreducible.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Irreducible (specRest (algebraMap k (GenParField k e n)) g (genPar k e n))

def NormFormDvd.Statement : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (n : ℕ) (x : Fin n → A) (p : MvPolynomial (Fin n) R),
      (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) ∣ p.map (algebraMap R A) →
        normForm A x ∣ p ^ Module.finrank R A

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

