module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0013

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscLat

open Module

variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] in
theorem trace_algebraMap_mul (c : ι) (r : R) (z : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * z) =
      algebraMap R F r * Algebra.trace F (L c) z := by
  rw [IsScalarTower.algebraMap_apply R F (L c), ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] in
theorem trace_term (c : ι) (r r' : R) (h x y : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y))) =
      algebraMap R F r * Algebra.trace F (L c) (h * h * x * y) * algebraMap R F r' := by
  have e : algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y)) =
      algebraMap R (L c) r * (algebraMap R (L c) r' * (h * h * x * y)) := by ring
  rw [e, trace_algebraMap_mul, trace_algebraMap_mul]
  ring

theorem sum_three_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem lattice_main {ϖ : R} (hϖ : Irreducible ϖ) (g : ∀ c, L c) (hg : ∀ c, g c ≠ 0)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c)
    (hb : ∀ k c, g c * b k c ∈ integralClosure R (L c)) (hli : LinearIndependent F b) :
    ∃ n t : ℕ, ∃ u : Rˣ,
      Module.length R
        (↥(Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}) ⧸
          (Submodule.span R (Set.range b)).comap
            (Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}).subtype) = n ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          (∏ c, Algebra.norm F (g c)) ^ 2 = algebraMap R F (↑u * ϖ ^ (2 * n + t)) := by
  classical
  have hB : ∀ c, Module.Finite R (integralClosure R (L c)) ∧
      Module.Free R (integralClosure R (L c)) ∧
      finrank R (integralClosure R (L c)) = finrank F (L c) := fun c => by
    obtain ⟨_, h1, h2, h3, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank R F (L c)
    exact ⟨h1, h2, h3⟩
  haveI : ∀ c, Module.Finite R (integralClosure R (L c)) := fun c => (hB c).1
  haveI : ∀ c, Module.Free R (integralClosure R (L c)) := fun c => (hB c).2.1
  let a := fun c => Module.Free.chooseBasis R (integralClosure R (L c))
  let α := Pi.basis a
  have hcard : Fintype.card (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) = m := by
    rw [hm, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Module.finrank_eq_card_chooseBasisIndex, (hB c).2.2]
  let σ := Fintype.equivFinOfCardEq hcard
  let φ : (∀ c, integralClosure R (L c)) →ₗ[R] (∀ c, L c) :=
    LinearMap.pi fun c => (LinearMap.mulLeft R (g c)⁻¹) ∘ₗ
      (integralClosure R (L c)).val.toLinearMap ∘ₗ LinearMap.proj c
  have hφ : ∀ x c, φ x c = (g c)⁻¹ * (x c : L c) := fun x c => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext c
    apply Subtype.ext
    have := congrFun hxy c
    rw [hφ, hφ] at this
    exact mul_left_cancel₀ (inv_ne_zero (hg c)) this
  have hSA : Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)} =
      LinearMap.range φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      refine ⟨fun c => ⟨g c * y c, hy c⟩, ?_⟩
      funext c
      rw [hφ]
      simp [← mul_assoc, inv_mul_cancel₀ (hg c)]
    · rintro _ ⟨x, rfl⟩
      apply Submodule.subset_span
      intro c
      rw [hφ, ← mul_assoc, mul_inv_cancel₀ (hg c), one_mul]
      exact (x c).2
  let b' : Fin m → ∀ c, integralClosure R (L c) := fun k c => ⟨g c * b k c, hb k c⟩
  have hb' : φ ∘ b' = b := by
    funext k c
    simp only [Function.comp_apply]
    rw [hφ]
    simp [b', ← mul_assoc, inv_mul_cancel₀ (hg c)]
  have hliR : LinearIndependent R b :=
    hli.restrict_scalars (by
      intro x y hxy
      simp only [Algebra.smul_def, mul_one] at hxy
      exact IsFractionRing.injective R F hxy)
  have hli' : LinearIndependent R b' := LinearIndependent.of_comp φ (by rw [hb']; exact hliR)
  obtain ⟨n, u, hlen, hdet⟩ := length_quot hϖ α φ hφinj _ hSA b' hli' σ
  rw [hb'] at hlen
  set T := α.toMatrix (b' ∘ σ) with hT
  have hdetT : T.det = ↑u * ϖ ^ n := by rw [hT, ← Basis.det_apply]; exact hdet
  have hexp : ∀ q c, ((b' (σ q) c : integralClosure R (L c)) : L c) =
      ∑ p, algebraMap R (L c) (T p q) * ((α p c : integralClosure R (L c)) : L c) := by
    intro q c
    have h1 := congrArg (fun x : (∀ c, integralClosure R (L c)) =>
      ((x c : integralClosure R (L c)) : L c)) (α.sum_repr (b' (σ q)))
    simp only [Finset.sum_apply, Pi.smul_apply] at h1
    rw [← h1]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hT,
      Basis.toMatrix_apply, Function.comp_apply]
    simp only [Algebra.smul_def]
  have hbexp : ∀ q c, b (σ q) c = ∑ p, algebraMap R (L c) (T p q) *
      ((g c)⁻¹ * ((α p c : integralClosure R (L c)) : L c)) := by
    intro q c
    have : b (σ q) c = (g c)⁻¹ * ((b' (σ q) c : integralClosure R (L c)) : L c) := by
      rw [← hb']; rfl
    rw [this, hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  let H : Matrix (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c)))
      (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) F :=
    Matrix.of fun p q => ∑ c, Algebra.trace F (L c) ((g c)⁻¹ * (g c)⁻¹ *
      ((α p c : integralClosure R (L c)) : L c) * ((α q c : integralClosure R (L c)) : L c))
  have hG : (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).submatrix σ σ =
      (T.map (algebraMap R F)).transpose * H * T.map (algebraMap R F) := by
    ext p' q'
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, H, hbexp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, trace_term]
    rw [sum_three_comm, Finset.sum_comm]
  have hH : H = Matrix.blockDiagonal' fun c => Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c)) := by
    ext ⟨c, i⟩ ⟨c', j⟩
    simp only [H, Matrix.of_apply, α, Pi.basis_apply]
    rw [Finset.sum_eq_single c]
    · by_cases hc : c = c'
      · subst hc
        simp [Matrix.blockDiagonal'_apply_eq]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc, Pi.single_eq_of_ne hc]
        simp
    · intro c'' _ hc''
      rw [Pi.single_eq_of_ne hc'']
      simp
    · simp
  haveI : ∀ c, IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (L c))
      (nonZeroDivisors R)) (L c) := fun c =>
    IsIntegralClosure.isLocalization R F (L c) (integralClosure R (L c))
  let a' := fun c => (a c).localizationLocalization F (nonZeroDivisors R) (L c)
  have hblock : ∀ c, (Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c))).det =
      Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * algebraMap R F (Algebra.discr R (a c)) := by
    intro c
    rw [← Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), ← gram_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, a', Module.Basis.localizationLocalization_apply]
    rfl
  have hd0 : ∀ c, Algebra.discr R (a c) ≠ 0 := by
    intro c h
    have := Algebra.discr_not_zero_of_basis F (a' c)
    rw [Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), h, map_zero] at this
    exact this rfl
  have hN : ∀ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * Algebra.norm F (g c) ^ 2 = 1 := by
    intro c
    have h1 : Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (hg c), map_one]
    rw [map_mul, sq]
    calc Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)⁻¹ * (Algebra.norm F (g c) * Algebra.norm F (g c))
        = (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) *
          (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) := by ring
      _ = 1 := by rw [h1, one_mul]
  have hprod : (∏ c, Algebra.discr R (a c)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
  obtain ⟨t, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hprod hϖ
  refine ⟨n, t, u * u * v, hlen, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self σ, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hH, det_blockDiagonal', Finset.prod_congr rfl fun c _ => hblock c]
  have hmap : (T.map (algebraMap R F)).det = algebraMap R F T.det := by
    rw [RingHom.map_det]; rfl
  rw [hmap, hdetT, Finset.prod_mul_distrib, ← map_prod, hv]
  have hNN : (∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2 = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => hN c
  calc algebraMap R F (↑u * ϖ ^ n) * ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) *
          algebraMap R F (↑v * ϖ ^ t)) * algebraMap R F (↑u * ϖ ^ n) * (∏ c, Algebra.norm F (g c)) ^ 2
      = algebraMap R F (↑u * ϖ ^ n) * algebraMap R F (↑v * ϖ ^ t) * algebraMap R F (↑u * ϖ ^ n) *
          ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2) := by ring
    _ = algebraMap R F (↑(u * u * v) * ϖ ^ (2 * n + t)) := by
      rw [hNN, mul_one, ← map_mul, ← map_mul]
      congr 1
      rw [Units.val_mul, Units.val_mul, pow_add, pow_mul]
      ring

end HDiscLat

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

section
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

noncomputable abbrev algOTKT : Algebra (OT K D N) (KTf K D N) :=
  ((algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)).toAlgebra

noncomputable abbrev algOpKT (la : HeightOneSpectrum (𝓞 K)) : Algebra (Op D N la) (KTf K D N) :=
  (OpToKT D N la).toAlgebra

theorem isFractionRing_OT :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by
  set_option synthInstance.maxHeartbeats 200000 in
  letI := algOTKT (K := K) D N
  have hinj : Function.Injective (algebraMap (OT K D N) (KTf K D N)) :=
    (IsFractionRing.injective (KTp K D N) (KTf K D N)).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  haveI : FaithfulSMul (OT K D N) (KTf K D N) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (KTp K D N) z
  letI : Algebra (OT K D N) (KTp K D N) := MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := TVar D N) (nonZeroDivisors (𝓞 K)) K
  obtain ⟨⟨P, ⟨_, a, ha, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) p
  obtain ⟨⟨Q, ⟨_, b, hb, rfl⟩⟩, hQ⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) q
  refine ⟨P * MvPolynomial.C b, Q * MvPolynomial.C a, ?_⟩
  have e : ∀ X : OT K D N, algebraMap (OT K D N) (KTf K D N) X =
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) X) := fun X => rfl
  have hC : ∀ c ∈ nonZeroDivisors (𝓞 K),
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) (MvPolynomial.C c)) ≠ 0 := by
    intro c hc
    rw [← e]
    exact (map_ne_zero_iff _ hinj).mpr (by
      rw [Ne, MvPolynomial.C_eq_zero]; exact nonZeroDivisors.ne_zero hc)
  have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
      (nonZeroDivisors.ne_zero hq)
  simp only at hP hQ
  rw [e, e, map_mul, map_mul, map_mul, map_mul, ← hP, ← hQ, map_mul, map_mul]
  have ha := hC a ha
  have hb := hC b hb
  field_simp

theorem isFractionRing_Op (la : HeightOneSpectrum (𝓞 K)) :
    letI := algOpKT (K := K) D N la
    IsFractionRing (Op D N la) (KTf K D N) := by
  set_option synthInstance.maxHeartbeats 200000 in
  letI := algOTKT (K := K) D N
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_OT (K := K) D N
  haveI : IsScalarTower (OT K D N) (Op D N la) (KTf K D N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = OpToKT D N la (algebraMap _ _ x)
      rw [OpToKT, IsLocalization.lift_eq]
      rfl
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT D N la).primeCompl
    (Op D N la) (KTf K D N)

theorem OpToKT_injective (la : HeightOneSpectrum (𝓞 K)) : Function.Injective (OpToKT D N la) := by
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_Op (K := K) D N la
  exact IsFractionRing.injective (Op D N la) (KTf K D N)

omit [NumberField K] in
theorem unif_mem [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by
  have hex : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    refine ⟨π, ?_, ?_⟩
    · rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    · rw [← la.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]
      norm_num
  rw [Data.unif, dite_eq_left hex]
  exact hex.choose_spec

noncomputable def unifOp (la : HeightOneSpectrum (𝓞 K)) : Op D N la :=
  algebraMap (OT K D N) (Op D N la) (MvPolynomial.C (Data.unif la))

theorem unifOp_irreducible (la : HeightOneSpectrum (𝓞 K)) : Irreducible (unifOp D N la) := by
  classical
  haveI := Op_isDVR (K := K) D N la
  obtain ⟨hmem, hnot⟩ := unif_mem la
  have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
    IsLocalization.injective (Op D N la) (laT D N la).primeCompl_le_nonZeroDivisors
  have hne : unifOp D N la ≠ 0 := by
    intro h
    have h0 : MvPolynomial.C (Data.unif la) = (0 : OT K D N) := hinj (h.trans (map_zero _).symm)
    rw [MvPolynomial.C_eq_zero] at h0
    exact hnot (h0 ▸ zero_mem _)
  have hmax : unifOp D N la ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [unifOp, IsLocalization.AtPrime.to_map_mem_maximal_iff (Op D N la) (laT D N la)]
    exact Ideal.mem_map_of_mem _ hmem
  have hnu : ¬ IsUnit (unifOp D N la) := (IsLocalRing.mem_maximalIdeal _).mp hmax
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Op D N la)
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  rcases j with _ | _ | j
  · exact absurd (by rw [hu, pow_zero, mul_one]; exact u.isUnit) hnu
  · rw [hu, pow_one]
    exact (irreducible_isUnit_mul u.isUnit).mpr hϖ
  · exfalso
    have h2 : unifOp D N la ∈ (IsLocalRing.maximalIdeal (Op D N la)) ^ 2 := by
      have hpow : (u : Op D N la) * ϖ ^ (j + 1 + 1) = (u * ϖ ^ j) * (ϖ * ϖ) := by ring
      rw [hu, hpow, pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hϖm hϖm)
    have hL2 : laT D N la ^ 2 = Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) (la.asIdeal ^ 2) := by
      unfold laT
      rw [Ideal.map_pow]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, hL2,
      IsLocalization.mem_map_algebraMap_iff (laT D N la).primeCompl (Op D N la)] at h2
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := h2
    simp only [unifOp, ← map_mul] at hx
    have hx' := hinj hx
    rw [← hx', MvPolynomial.mem_map_C_iff] at ha
    have hs' : s ∉ Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal := hs
    rw [MvPolynomial.mem_map_C_iff, not_forall] at hs'
    obtain ⟨mm, hmm⟩ := hs'
    have h3 := ha mm
    rw [MvPolynomial.coeff_C_mul] at h3
    have v1 : la.intValuation (Data.unif la) = la.intValuation (Data.unif la) * la.intValuation (AddMonoidAlgebra.coeff s mm) := by
      have : la.intValuation (AddMonoidAlgebra.coeff s mm) = 1 := by
        apply le_antisymm (la.intValuation_le_one _)
        rw [← not_lt, la.intValuation_lt_one_iff_mem]
        exact hmm
      rw [this, mul_one]
    have h4 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [v1, ← map_mul]
      exact (la.intValuation_le_pow_iff_mem _ 2).mpr h3
    exact hnot ((la.intValuation_le_pow_iff_mem _ 2).mp h4)

theorem algK_unif (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by
  rw [unifOp, OpToKT, IsLocalization.lift_eq, RingHom.comp_apply, OTtoKT, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]

theorem exp_unique (la : HeightOneSpectrum (𝓞 K)) {m m' : ℤ} {u u' : Op D N la} (hu : IsUnit u)
    (hu' : IsUnit u')
    (h : (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u') : m = m' := by
  have key : ∀ {m m' : ℤ} {u u' : Op D N la}, IsUnit u → IsUnit u' →
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
        (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u' → m ≤ m' := by
    intro m m' u u' hu hu' h
    by_contra hlt
    push_neg at hlt
    have hϖ0 : algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
      rw [algK_unif]
      exact (map_ne_zero_iff _ (OpToKT_injective D N la)).mpr (unifOp_irreducible D N la).ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = m' + (k + 1 : ℕ) := ⟨(m - m' - 1).toNat, by omega⟩
    rw [hk, zpow_add₀ hϖ0, mul_assoc] at h
    have h' := mul_left_cancel₀ (zpow_ne_zero m' hϖ0) h
    rw [zpow_natCast, algK_unif, ← map_pow, ← map_mul] at h'
    have h'' := OpToKT_injective D N la h'
    have hunit : IsUnit (unifOp D N la ^ (k + 1) * u) := h'' ▸ hu'
    have := isUnit_of_mul_isUnit_left hunit
    exact (unifOp_irreducible D N la).not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp this)
  exact le_antisymm (key hu hu' h) (key hu' hu h.symm)

end

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem gOrd_eq (d : Data K ι Ω WT A) (la : HeightOneSpectrum (𝓞 K)) {q : KTf K d.D d.N} {m : ℤ}
    {u : Op d.D d.N la} (hu : IsUnit u)
    (hq : q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u) :
    d.gOrd la q = m := by
  classical
  have hex : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u :=
    ⟨m, u, hu, hq⟩
  rw [gOrd, dite_eq_left hex]
  obtain ⟨u', hu', hq'⟩ := hex.choose_spec
  exact exp_unique d.D d.N la hu' hu (hq'.symm.trans hq)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt
section
set_option linter.unusedVariables false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace LeafSt

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)

def PlaceTrivialOrPositive : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p),
  (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)

def AdmissibleValuationPrimeUnique : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton

def GeneratorMultiHomogeneous : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)

def places_over_la : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι),
  (d.PlOver la c).Finite ∧
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
        (d.fze h c w : ℤ) * ramIdx (K := K) (d.Wres c w) la) = d.delc c

def exists_generic : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1),
  (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0)

end LeafSt

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHor
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem reg_horizontal {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  exact reg_horizontal_pf P hh hmeet e he f hdvr hf

end ReciprocityTheory.ChartRestriction.G.T0
end

