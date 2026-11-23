module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (P J : Ideal A) (ψ : A ⧸ P →+* L)
    (hloc : IsLocalHom (ψ.comp (Ideal.Quotient.mk P))) (hflat : ψ.Flat)
    (hmax : (IsLocalRing.maximalIdeal A).map (ψ.comp (Ideal.Quotient.mk P)) =
      IsLocalRing.maximalIdeal L) :
    Module.length L (L ⧸ J.map (ψ.comp (Ideal.Quotient.mk P))) =
      Module.length A (A ⧸ (P ⊔ J)) := by
  have : Nontrivial (A ⧸ P) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg ψ h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := ψ.toAlgebra
  have : Module.Flat (A ⧸ P) L := hflat
  have : IsLocalHom (algebraMap (A ⧸ P) L) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hloc.map_nonunit a ha).map _
  have hq : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk P) =
      IsLocalRing.maximalIdeal (A ⧸ P) := by
    have h : (IsLocalRing.maximalIdeal (A ⧸ P)).comap (Ideal.Quotient.mk P) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hmax' : (IsLocalRing.maximalIdeal (A ⧸ P)).map (algebraMap (A ⧸ P) L) =
      IsLocalRing.maximalIdeal L := by
    rw [← hq, Ideal.map_map]
    exact hmax
  have key := IsLocalRing.length_baseChange (A ⧸ P) L ((A ⧸ P) ⧸ J.map (Ideal.Quotient.mk P))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L
    (J.map (Ideal.Quotient.mk P))).toLinearEquiv.length_eq, hmax'] at key
  have h1 : Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one, Ideal.map_map, RingHom.algebraMap_toAlgebra] at key
  rw [key, ← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A P J).toLinearEquiv.length_eq

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem secLin_eq_mk_map {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by
  rw [secLin, map_linForm]

theorem SpecLength.proof (h1 : SpecChart.Statement) (h2 : FiniteOrd.Statement)
    (h3 : ParDVRIsDVR.Statement) (h4 : SecBFinite.Statement) (h5 : SecBLinInj.Statement) :
    SpecLength.Statement := by
  classical
  intro K _ _ n e I f u v hI hf hu 𝔫 W hW hWn
  have hWp : W.IsPrime := hW.1.1.1
  obtain ⟨ψ, hψ, hloc, hflat, hmax⟩ := h1 K n e I v hI 𝔫 W hW hWn
  have := h3 K e n v
  have := h4 K n e I f v hI hf
  have hfin := h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫
  have hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
      (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) =
      (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u)) := by
    rw [RingHom.comp_apply, hψ]
    exact congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)
  have hlen0 := length_quot_map_of_flat (A := Localization.AtPrime W)
    (L := Localization.AtPrime 𝔫.asIdeal)
    (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
    (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat
  have hlen := hlen0 hmax
  rw [Ideal.map_span, Set.image_singleton, ← hx] at hlen
  have hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W =
      (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸
        ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
          Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat := by
    rw [localMult, dite_eq_left hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  unfold Ring.ord at hfin ⊢
  rw [hlen] at hfin ⊢
  split_ifs with hlW
  · rw [hmult, ENat.natCast_toNat hfin]
  · have hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW
    have htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
        Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤ :=
      eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)
    rw [htop]
    have : Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem secIdealOf_eq_map (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : secIdealOf e I v W = W.map (toSecB e I v) :=
  Ideal.map_map _ _

theorem toSecB_C (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    toSecB e I v (C a) = algebraMap (ParDVR e n v) (SecB e I v)
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  simp only [toSecB, RingHom.comp_apply, MvPolynomial.map_C]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

omit [NumberField K] in
theorem mem_maximalIdeal_of_mem (e : ℕ) (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a) ∈
      IsLocalRing.maximalIdeal (ParDVR e n v) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (ParDVR e n v) (parPrime e n v) _).mpr (Ideal.mem_map_of_mem _ ha)

theorem exists_secCoord_not_mem (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (J : Ideal (SecB e I v)) (hJ : J ≠ ⊤) : ∃ j, toSecB e I v (X j) ∉ J := by
  by_contra! h
  apply hJ
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, chartForm, linForm, map_sum]
  refine J.sum_mem fun j _ => ?_
  rw [map_mul]
  refine J.mul_mem_left _ ?_
  simpa [toSecB] using h j

theorem SpecMax.proof (h1 : SecBFinite.Statement) (h2 : SecIdealOfPrime.Statement) : SpecMax.Statement := by
  intro K _ _ n e I f v hI hf
  have := h1 K n e I f v hI hf
  have hcomp : ∀ W ∈ specComps I v, integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := fun W hW => hW.1.1.2

  have hmax : ∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal := by
    intro W hW
    obtain ⟨hprime, -⟩ := h2 K n e I f v hI hf W hW
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap (ParDVR e n v) (SecB e I v)) (algebraMap_isIntegral_iff.mpr inferInstance)
      (secIdealOf e I v W) ?_
    have hle : IsLocalRing.maximalIdeal (ParDVR e n v) ≤
        (secIdealOf e I v W).comap (algebraMap (ParDVR e n v) (SecB e I v)) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      change Ideal.map C v.asIdeal ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap]
      rw [← toSecB_C, secIdealOf_eq_map]
      exact Ideal.mem_map_of_mem _ (hcomp W hW (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨hmax, fun 𝔫 h𝔫 => ?_⟩

  set W' := 𝔫.comap (toSecB e I v) with hW'
  have hR : 𝔫.comap (algebraMap (ParDVR e n v) (SecB e I v)) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap (ParDVR e n v) (SecB e I v)) (algebraMap_isIntegral_iff.mpr inferInstance) 𝔫)
  have hle : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W' := by
    refine sup_le (fun p hp => ?_) ?_
    · have h0 : toSecB e I v p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
      rw [hW', Ideal.mem_comap, h0]
      exact 𝔫.zero_mem
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hW', Ideal.mem_comap, toSecB_C, ← Ideal.mem_comap, hR]
      exact mem_maximalIdeal_of_mem e v ha
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le (J := W') hle
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 h𝔫.ne_top
  have hW : W ∈ specComps I v := ⟨hWmin, ⟨j, fun h => hj (hWle h)⟩⟩
  have heq : secIdealOf e I v W = 𝔫 := by
    refine (hmax W hW).eq_of_le h𝔫.ne_top ?_
    rw [secIdealOf_eq_map, Ideal.map_le_iff_le_comap]
    exact hWle
  refine ⟨W, ⟨hW, heq⟩, fun W₁ ⟨hW₁, heq₁⟩ => ?_⟩
  rw [← (h2 K n e I f v hI hf W₁ hW₁).2, ← (h2 K n e I f v hI hf W hW).2, heq, heq₁]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecResidue.proof (hCSD : ChowSecDegree.Statement) (hCNF : ChowNormForm.Statement)
    (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) : SpecResidue.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  obtain ⟨hQ, hQdim⟩ := hDim K n e I f v hI hf W hW
  obtain ⟨g, hg⟩ := hExist k n (e + 1) (reduceMod v W) hQ hQdim
  have hind := hInd K e n v
  have hfin := (hCNF k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg).1
  have hdeg := hCSD k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg

  let ι : 𝓞 K →+* R := algebraMap (𝓞 K) R
  let ρ : R →+* E := algebraMap R E
  have hρ : Function.Surjective ρ := Ideal.algebraMap_residueField_surjective _
  let Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E := MvPolynomial.map ρ
  have hΨ : Function.Surjective Ψ := MvPolynomial.map_surjective _ hρ
  have hcomp : ρ.comp ι = (algebraMap k E).comp (algebraMap (𝓞 K) k) := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap _ _ _ _ a).symm
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p

  have hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := hW.1.1.2
  let WR : Ideal (MvPolynomial (Fin n) R) := W.map (MvPolynomial.map ι)
  let S := secIdeal (modelR e I v) (parY e n v)
  let QE := (reduceMod v W).map (MvPolynomial.map (algebraMap k E))
  let T := secIdeal QE (parYκ e n v)
  have hWR : WR.map Ψ = QE := by
    simp only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]
    rfl
  have hM : (modelR e I v).map Ψ ≤ QE := by
    rw [← hWR]
    exact Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))
  have hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ =
      Ideal.span (Set.range (secForm (parYκ e n v))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [Ψ, secForm, linForm, parYκ, ρ]
    rfl
  have hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ =
      Ideal.span {chartForm (parYκ e n v) - 1} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Ψ, chartForm, linForm, parYκ, ρ]
    rfl
  have hT : (S ⊔ WR).map Ψ = T := by
    simp only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hkerΨ : RingHom.ker Ψ ≤ WR := by
    have h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C :=
      IsScalarTower.algebraMap_eq _ _ _
    have hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι := by
      rw [h1, ← Ideal.map_map]
      exact Localization.AtPrime.map_eq_maximalIdeal.symm
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map,
      ← MvPolynomial.map_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono (le_sup_right.trans hJW)

  let Φ : MvPolynomial (Fin n) R →ₐ[R] SecAlg QE (parYκ e n v) :=
    { toRingHom := (Ideal.Quotient.mk T).comp Ψ
      commutes' := fun r ↦ by
        simp [Ψ, ρ]
        rfl }
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp hΨ
  have hker : RingHom.ker Φ = S ⊔ WR := by
    have : RingHom.ker Φ = T.comap Ψ := by
      ext x
      simp [Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hkerΨ.trans le_sup_right)
  have hsec : secIdealOf e I v W = WR.map (Ideal.Quotient.mkₐ R S) := rfl
  let eq : (SecB e I v ⧸ secIdealOf e I v W) ≃ₐ[R] SecAlg QE (parYκ e n v) :=
    ((Ideal.quotientEquivAlgOfEq R hsec).trans (DoubleQuot.quotQuotEquivQuotSupₐ R S WR)).trans
      ((Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hΦ))
  rw [eq.toLinearEquiv.length_eq, Module.length_eq_of_surjective hρ, Module.length_eq_finrank,
    hdeg]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def DerivSpanTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [PerfectField k] [Field L] [Algebra k L] (ι : Type) [Fintype ι]
    (z : ι → L) (e : ℕ),
    Algebra.trdeg k (Algebra.adjoin k (Set.range z)) ≤ (e : Cardinal) →
    ∃ r ≤ e, ∃ b : Fin r → ι → IntermediateField.adjoin k (Set.range z),
      ∀ D : Derivation k L L, ∃ c : Fin r → L, ∀ j, D (z j) = ∑ m, c m * (b m j : L)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenSecKer.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      RingHom.ker ((Ideal.Quotient.mk
          (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
        (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenericFormsKer.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] (ι : Type) [Fintype ι] (e r : ℕ), r ≤ e →
    ∀ (u : Fin e × ι → L), AlgebraicIndependent F u →
    ∀ (b : Fin r → ι → F) (c : Fin r → L),
      (∀ i : Fin e, ∑ j, u (i, j) * ∑ m, c m * algebraMap F L (b m j) = 0) →
      ∀ j, ∑ m, c m * algebraMap F L (b m j) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def SecPointSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (L : Type) [Field L] [Algebra k L]
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    [Module.Finite (GenParField k e n) L] (x : Fin n → L),
    Algebra.adjoin (GenParField k e n) (Set.range x) = ⊤ →
    (∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0) →
    ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1 →
    (∀ j₀, x j₀ ≠ 0 →
      Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable (GenParField k e n) L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

