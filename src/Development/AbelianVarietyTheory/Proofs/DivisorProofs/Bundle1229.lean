module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem height_ge_of_X_sub_C_mem : ∀ {F : Type} [Field F] (m : ℕ) (c : Fin m → F) (P : Ideal (MvPolynomial (Fin m) F))
    [P.IsPrime], (∀ i, MvPolynomial.X i - MvPolynomial.C (c i) ∈ P) → (m : ℕ∞) ≤ P.height := by
  intro F _ m c P _ hP
  have hmk : ∀ f : MvPolynomial (Fin m) F,
      Ideal.Quotient.mk P f = Ideal.Quotient.mk P (MvPolynomial.C (MvPolynomial.eval c f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), map_add (f := _)]
    | mul_X p i hp =>
      have hi : Ideal.Quotient.mk P (MvPolynomial.X i) = Ideal.Quotient.mk P (MvPolynomial.C (c i)) :=
        Ideal.Quotient.eq.2 (hP i)
      rw [map_mul, hp, hi, ← map_mul, ← map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.C_mul]
  have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp MvPolynomial.C) := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨MvPolynomial.eval c f, (hmk f).symm⟩
  have hmax : P.IsMaximal := by
    let e := RingEquiv.ofBijective _ ⟨((Ideal.Quotient.mk P).comp MvPolynomial.C).injective, hsurj⟩
    exact Ideal.Quotient.maximal_of_isField P (MulEquiv.isField (Field.toIsField F) e.symm.toMulEquiv)
  have htr : Algebra.trdeg F (MvPolynomial (Fin m) F) = m := by
    have h2 := (IsTranscendenceBasis.mvPolynomial (Fin m) F).cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin] at h2
    exact h2.symm
  rw [ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field m htr P]

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra (K ⊗[ℂ] κ') L]

theorem height_le_height_of_flat {A : Subalgebra ℂ K} {m : ℕ} (v : Fin m → A)
    (hf : (polyMap (κ' := κ') A v).Flat) (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    (𝔭.comap (polyMap A v)).height ≤ 𝔭.height := by
  letI := (polyMap (κ' := κ') A v).toAlgebra
  haveI : Module.Flat (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) := hf
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) :=
    Algebra.HasGoingDown.of_flat
  set q := 𝔭.comap (polyMap (κ' := κ') A v) with hq
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : 𝔭.LiesOver q := ⟨rfl⟩
  obtain ⟨l, hl, hlen⟩ := q.exists_ltSeries_length_eq_height
  haveI : 𝔭.LiesOver l.last.asIdeal := by rw [hl]; infer_instance
  obtain ⟨L', hlen', hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔭
  rw [← hlen, ← hlen', (⟨𝔭, ‹_›⟩ : PrimeSpectrum (tens (κ' := κ') A)).height_eq_orderHeight]
  exact Order.length_le_height (le_of_eq hlast)

theorem ringKrullDim_locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) :
    ringKrullDim (locAt (L := L) 𝔭) = 𝔭.height := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  haveI : IsLocalization.AtPrime (locAt (L := L) 𝔭) 𝔭 :=
    { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
      surj := fun x => by
        obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
        exact ⟨(a, ⟨s, hs⟩), e⟩
      exists_of_eq := fun {a b} e => ⟨1, by
        have : a = b := Subtype.ext (hinj (congrArg Subtype.val e))
        rw [this]⟩ }
  exact IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 _

theorem dim_locAt_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ k R π ρ E 𝔭 _ hO' hc1 hc2 hfrac hER hcent hz h𝔭
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  obtain ⟨zR, hzR⟩ := _root_.GlobalTheory.GraphLocal.exists_trBasis_lift k R π hfrac hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  rw [ringKrullDim_locAt 𝔭 hinj]
  apply le_antisymm
  ·
    rw [← ringKrullDim_locAt 𝔭 hinj]
    letI : Algebra ℂ L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
    haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq' rfl
    have hQ := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor (L := L) E 𝔭 hO'
    letI : IsLocalRing (locAt (L := L) 𝔭) := isLocalRing_locAt 𝔭 hinj
    letI : Algebra ℂ (locAt (L := L) 𝔭) :=
      ((algebraMap ℂ L).codRestrict _ hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ (locAt (L := L) 𝔭) := hQ.essFiniteType
    haveI : IsNoetherianRing (locAt (L := L) 𝔭) := Algebra.EssFiniteType.isNoetherianRing ℂ _
    have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hc1 hc2 hfrac hcent ht hzR h𝔭
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [hmax]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := locAt (L := L) 𝔭)
      (Set.finite_range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i))
    have h2 : (Set.range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i)).ncard ≤ k + 1 := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    have h3 := h1.trans h2
    exact_mod_cast h3
  ·
    have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have hzR' : IsTranscendenceBasis ℂ (fun i => π (zR i)) := by
      unfold TrBasis at hzR; rw [e] at hzR; exact hzR
    let v : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))
    have hf := GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval (κ' := κ') (placeAlg E) (k + 1) v
      (GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts k R π E hER t zR hc1 hc2 hcent ht hzR'.1)
    have hle := height_le_height_of_flat v hf 𝔭
    have hgr : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
    have hX : ∀ i, MvPolynomial.X i - MvPolynomial.C ((Fin.cons (0 : κ') fun j => ρ (π (zR j)) :
        Fin (k + 1) → κ') i) ∈ 𝔭.comap (polyMap (κ' := κ') (placeAlg E) v) := by
      intro i
      rw [Ideal.mem_comap]
      apply hgr
      apply Ideal.subset_span
      refine Fin.cases ?_ (fun j => ?_) i
      · left
        refine ⟨(t : K), ?_, ?_⟩
        · rw [E.ord_irreducible ht]; exact one_pos
        · simp [v]
      · right
        refine ⟨zR j, ?_⟩
        simp [v]
    have hB3 := height_ge_of_X_sub_C_mem (k + 1) _ _ hX
    have := hB3.trans hle
    exact_mod_cast this

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_sigma (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : E) : w.valuation E (σ x) = w.valuation E x :=
  _root_.GlobalTheory.InertConjVal.val_conj F E σ v w h x

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : F) : w.valuation E (algebraMap F E x) = v.valuation F x :=
  _root_.GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w h x

theorem exists_max_dual (w : HeightOneSpectrum (𝓞 E)) : ∃ e : E, e ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
    ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e :=
  _root_.GlobalTheory.invDifferent_exists_max_valuation E w

theorem exists_local_basis (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) : ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
    ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 :=
  GlobalTheory.exists_local_basis_of_isLattice E w n L hL

theorem exists_den (w : HeightOneSpectrum (𝓞 E)) (a : E) (ha : w.valuation E a ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r :=
  _root_.GlobalTheory.IntegralDenom.exists_denom_not_mem E w a ha

theorem exists_common_den (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (hσ : ∀ x, w.valuation E (σ x) = w.valuation E x)
    (hden : ∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r)
    (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (X : Matrix (Fin n) (Fin n) E)
    (hX : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r :=
  _root_.GlobalTheory.ConjCoordDenom.exists_common_denom_conj_coords F E σ w hσ hden n L hL X hX

theorem dual_bound (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hXc : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1)
    (s : 𝓞 E) (hs : s ∉ w.asIdeal) (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) :
    ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 :=
  GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral F E σ n J L w hdual X hX hG hXc s hs hsr e he

theorem val_det_le (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E)
    (c : WithZero (Multiplicative ℤ)) (h : ∀ i j, w.valuation E (M i j) ≤ c) :
    w.valuation E M.det ≤ c ^ n := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le _ fun p _ => ?_
  have hp : w.valuation E (∏ i, M (p i) i) ≤ c ^ n := by
    rw [map_prod]
    calc ∏ i, w.valuation E (M (p i) i) ≤ ∏ _i : Fin n, c := Finset.prod_le_prod' fun i _ => h _ _
      _ = c ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1 <;> rw [h1]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, Valuation.map_neg]

end GlobalTheory.SkewDetParity

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_cols (σ : E →ₐ[F] E) {n : ℕ} (J X : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Xᵀ * J * X.map σ) i j = form σ J (fun k => X k i) (fun k => X k j) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem parity_at (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E)
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (hn : Even n) (hJ : J.det ≠ 0) : ∃ a : E, a ≠ 0 ∧ w.valuation E J.det = w.valuation E a ^ 2 := by
  obtain ⟨e, he0, heD, hemax⟩ := exists_max_dual w
  obtain ⟨X, hXu, hXL, hXc⟩ := exists_local_basis w n L hL
  obtain ⟨s, hs, hsr⟩ := exists_common_den σ w (val_sigma σ v w hin) (exists_den w) n L hL.fg X hXc
  have hσdet : σ X.det = (X.map σ).det := by
    rw [AlgHom.map_det]; rfl
  have hdetG : (Xᵀ * J * X.map σ).det = X.det * J.det * σ X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hσdet]
  have hX0 : X.det ≠ 0 := hXu.ne_zero
  have hσX0 : σ X.det ≠ 0 := by
    intro h0; apply hX0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hG0 : (Xᵀ * J * X.map σ).det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (mul_ne_zero hX0 hJ) hσX0
  have hGu : IsUnit (Xᵀ * J * X.map σ).det := isUnit_iff_ne_zero.2 hG0
  have hGij : ∀ i j, w.valuation E ((Xᵀ * J * X.map σ) i j) ≤ w.valuation E e := fun i j => by
    rw [form_cols]
    exact hemax _ fun o => (hdual _).1 (hXL i) _ (hXL j) o
  have hup := val_det_le w _ _ hGij
  have hinv := dual_bound σ n J L w hdual X hXu hGu hXc s hs hsr e heD
  have hlow := val_det_le w (e • (Xᵀ * J * X.map σ)⁻¹) 1 (fun i k => by
    simpa [Matrix.smul_apply] using hinv i k)
  rw [one_pow, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, map_mul,
    map_pow, map_inv₀] at hlow
  have hvG0 : w.valuation E (Xᵀ * J * X.map σ).det ≠ 0 := (Valuation.ne_zero_iff _).2 hG0
  have hlow' : w.valuation E e ^ n ≤ w.valuation E (Xᵀ * J * X.map σ).det := by
    first
      | rwa [mul_inv_le_iff₀ hvG0, one_mul] at hlow
      | rwa [mul_inv_le_iff₀ (zero_lt_iff.2 hvG0), one_mul] at hlow
  have hEq : w.valuation E (Xᵀ * J * X.map σ).det = w.valuation E e ^ n := le_antisymm hup hlow'
  rw [hdetG, map_mul, map_mul, val_sigma σ v w hin] at hEq
  obtain ⟨m, rfl⟩ := hn
  refine ⟨e ^ m / X.det, div_ne_zero (pow_ne_zero _ he0) hX0, ?_⟩
  have hvX0 : w.valuation E X.det ≠ 0 := (Valuation.ne_zero_iff _).2 hX0
  rw [map_div₀, map_pow, div_pow, ← pow_mul, mul_two, ← hEq]
  field_simp

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem det_eq_unit_mul_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  intro F E _ _ _ _ _ σ B hB n r s W hW hn v w hin _
  by_cases hJ : W.J.det = 0
  · exact ⟨0, 1, map_one _, by simp [hJ]⟩
  obtain ⟨a, ha0, hva⟩ := parity_at σ v w hin n W.J W.L hW.lat hW.dual hn hJ
  have hmap : W.J.map σ = -W.Jᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [← hW.skew j i]
  have hfix : σ W.J.det = W.J.det := by
    rw [AlgHom.map_det]
    change (W.J.map σ).det = _
    rw [hmap, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin, hn.neg_one_pow, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfix
  have hfixN : σ (a * σ a) = a * σ a := by
    rw [map_mul, sigma_sigma σ hB.cm, mul_comm]
  obtain ⟨β, hβ⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfixN
  have hσa0 : σ a ≠ 0 := by
    intro h0; apply ha0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, map_zero] at hβ; exact mul_ne_zero ha0 hσa0 hβ.symm
  refine ⟨(1 : Fv F v) ⊗ₜ[F] a, algebraMap F (Fv F v) (c / β), ?_, ?_⟩
  · rw [show Valued.v (algebraMap F (Fv F v) (c / β)) = v.valuation F (c / β) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c / β), ← val_algebraMap v w hin, map_div₀, map_div₀, hc, hβ,
      map_mul, val_sigma σ v w hin, hva, sq]
    have : w.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact div_self (mul_ne_zero this this)
  · have key : (algebraMap F (Fv F v) (c / β)) ⊗ₜ[F] (algebraMap F E β) = (1 : Fv F v) ⊗ₜ[F] W.J.det := by
      rw [Algebra.algebraMap_eq_smul_one (c / β), TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul,
        div_mul_cancel₀ _ hβ0, hc]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hβ,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← key]
    simp

end GlobalTheory.SkewDetParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFstSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem spMap_fst_surjective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) := by
  intro q
  haveI : q.asIdeal.IsPrime := q.2
  refine ⟨⟨q.asIdeal.comap (TrivSqZeroExt.inlHom R M), Ideal.IsPrime.comap _⟩, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  show (TrivSqZeroExt.inlHom R M) ((TrivSqZeroExt.fstHom R R M) a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
  have hm : TrivSqZeroExt.inr a.snd ∈ q.asIdeal :=
    q.2.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact q.asIdeal.zero_mem)
  have e : TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inr a.snd = a := TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  constructor
  · intro h
    rw [← e]
    exact q.asIdeal.add_mem h hm
  · intro h
    show TrivSqZeroExt.inl a.fst ∈ q.asIdeal
    rw [eq_sub_of_add_eq e]
    exact q.asIdeal.sub_mem h hm

theorem exists_basicOpen_inl {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] {X : Scheme.{0}} (x : Sp R ⟶ X) (q : Sp (TrivSqZeroExt R M)) :
    ∃ (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (U : X.affineOpens), q ∈ (Sp (TrivSqZeroExt R M)).basicOpen s ∧
      spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 := by
  obtain ⟨q₀, rfl⟩ := spMap_fst_surjective R M q
  obtain ⟨U, hUa, hU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x q₀ ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show q₀ ∈ ((x ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) from hU) (x ⁻¹ᵁ U).2
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv (TrivSqZeroExt.inl r), ⟨U, hUa⟩, ?_, ?_⟩
  · rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact hr
  · intro w hw
    rw [Scheme.Hom.mem_preimage, AlgebraicGeometry.basicOpen_eq_of_affine] at hw
    exact hle hw

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

end GlobalTheory.IdTorusCent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  first | exact @GlobalTheory.IsomPhi.phi_map | exact GlobalTheory.IsomPhi.phi_map | (intros; apply GlobalTheory.IsomPhi.phi_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLeviStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  first | exact @GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | exact GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | (intros; apply GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding <;> assumption)
end

