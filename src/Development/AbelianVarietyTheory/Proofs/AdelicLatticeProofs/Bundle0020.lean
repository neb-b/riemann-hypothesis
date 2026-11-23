module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutive
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyInv

variable {R : Type} [CommRing R] {n : ℕ}

theorem map_mul_map_inv (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    M.map σ * (M⁻¹).map σ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_add (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).map σ = 1 + M.map σ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_sub (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 - M).map σ = 1 - M.map σ := by
  rw [Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem one_add_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) + (1 - g) = (2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [two_smul]; abel
  calc 1 + (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := (Matrix.add_mul _ _ _).symm
    _ = (2 : R) • (1 + g)⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]

theorem one_sub_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 - (1 - g) * (1 + g)⁻¹ = (2 : R) • (g * (1 + g)⁻¹) := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) - (1 - g) = (2 : R) • g := by
    rw [two_smul]; abel
  calc 1 - (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := (Matrix.sub_mul _ _ _).symm
    _ = (2 : R) • (g * (1 + g)⁻¹) := by rw [h2, Matrix.smul_mul]

theorem one_add_cayley_mul (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by
  rw [one_add_cayley g h, smul_mul_smul_comm, hc, one_smul, Matrix.nonsing_inv_mul _ h]

private theorem eq_zero_of_mul_mul_eq_zero_of_isUnit_det (A B X : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * X * B = 0) : X = 0 := by
  calc X = (A⁻¹ * A) * X * (B * B⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
          Matrix.mul_one]
    _ = A⁻¹ * (A * X * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

private theorem isUnit_det_map_of_isUnit_det (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : IsUnit (M.map σ).det := by
  simpa [RingHom.map_det, RingHom.mapMatrix_apply] using h.map σ

theorem cayley_transform : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  intro R _ σ n G hσ hG hGu h2
  obtain ⟨c, hc⟩ := h2.exists_right_inv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg hP
    have hSP : (1 - g) * (1 + g)⁻¹ * (1 + g) = 1 - g := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + g)ᵀ) ((1 + g).map σ) _
        (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
      have e1 : (1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ = (1 - g)ᵀ := by
        rw [← Matrix.transpose_mul, hSP]
      have e2 : ((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ = (1 - g).map σ := by
        rw [← Matrix.map_mul, hSP]
      have e3 : (1 - gᵀ) * G * (1 + g.map σ) + (1 + gᵀ) * G * (1 - g.map σ)
          = (G - gᵀ * G * g.map σ) + (G - gᵀ * G * g.map σ) := by noncomm_ring
      calc (1 + g)ᵀ * (((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ)
            * (1 + g).map σ
          = ((1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ) * G * (1 + g).map σ
            + (1 + g)ᵀ * G * (((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (1 - g)ᵀ * G * (1 + g).map σ + (1 + g)ᵀ * G * (1 - g).map σ := by rw [e1, e2]
        _ = 0 := by
            rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
              map_one_add, map_one_sub, e3, hg, sub_self, add_zero]
    · rw [one_add_cayley g hP, Matrix.det_smul]
      exact (h2.pow _).mul (Matrix.isUnit_nonsing_inv_det _ hP)
  · intro g hP
    have hinv : (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = c • (1 + g) :=
      Matrix.inv_eq_right_inv (one_add_cayley_mul g hP c hc)
    rw [hinv, one_sub_cayley g hP, smul_mul_smul_comm, hc, one_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  · intro S hS hP
    have hgP : (1 - S) * (1 + S)⁻¹ * (1 + S) = 1 - S := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [← sub_eq_zero]
    apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + S)ᵀ) ((1 + S).map σ) _
      (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
    have e1 : (1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ = (1 - S)ᵀ := by
      rw [← Matrix.transpose_mul, hgP]
    have e2 : ((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ = (1 - S).map σ := by
      rw [← Matrix.map_mul, hgP]
    have e3 : (1 - Sᵀ) * G * (1 - S.map σ) - (1 + Sᵀ) * G * (1 + S.map σ)
        = -((Sᵀ * G + G * S.map σ) + (Sᵀ * G + G * S.map σ)) := by noncomm_ring
    calc (1 + S)ᵀ * (((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ - G)
          * (1 + S).map σ
        = ((1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ) * G
            * (((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ)
          - (1 + S)ᵀ * G * (1 + S).map σ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (1 - S)ᵀ * G * (1 - S).map σ - (1 + S)ᵀ * G * (1 + S).map σ := by rw [e1, e2]
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
            map_one_add, map_one_sub, e3, hS, add_zero, neg_zero]
  · intro A
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hKG : ((G⁻¹).map σ)ᵀ * G = 1 := by
      calc ((G⁻¹).map σ)ᵀ * G = ((G⁻¹).map σ)ᵀ * (G.map σ)ᵀ := by rw [hG]
        _ = (G.map σ * (G⁻¹).map σ)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [map_mul_map_inv σ G hGu, Matrix.transpose_one]
    have hGK : G * ((G⁻¹).map σ)ᵀ = 1 := by
      rw [← Matrix.inv_eq_left_inv hKG]
      exact Matrix.mul_nonsing_inv _ hGu
    have hAA : (A.map σ).map σ = A := by
      ext i j
      simp [hσ]
    have hT : (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ = Aᵀ - G * A.map σ * G⁻¹ := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose]
    have hTs : (A - (G * A.map σ * G⁻¹)ᵀ).map σ
        = A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G) := by
      rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul,
        hAA, Matrix.transpose_mul, Matrix.transpose_mul, hG]
    rw [hT, hTs]
    calc (Aᵀ - G * A.map σ * G⁻¹) * G + G * (A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G))
        = Aᵀ * G - G * A.map σ * (G⁻¹ * G)
          + (G * A.map σ - (G * ((G⁻¹).map σ)ᵀ) * (Aᵀ * G)) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by
          rw [hGinvG, hGK, Matrix.mul_one, Matrix.one_mul]
          abel

end GlobalTheory.CayleyInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpenStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_meets_finitely_many_leftCosets_open : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (K : Set G), IsOpen (U : Set G) → IsCompact K → ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  first | exact @GlobalTheory.ClassFin.compact_subset_finite_leftCosets | exact GlobalTheory.ClassFin.compact_subset_finite_leftCosets | (intros; apply GlobalTheory.ClassFin.compact_subset_finite_leftCosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow :
    ∀ (K : Type) [Field K] [NumberField K], Countable (Ideal (𝓞 K)) ∧ ∀ σ : ℝ, 1 < σ → (Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∧ Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  intro K _ _
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hU : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
      ext I; simp
    have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
      rw [hU]
      exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
    exact Set.countable_univ_iff.mp hc
  · have hsum : Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
      have h := _root_.GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
      refine h.congr fun I => ?_
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
      simp
    refine ⟨hsum, ?_⟩
    have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
      fun P Q h => HeightOneSpectrum.ext h
    exact hsum.comp_injective hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_admissiblePlaces_superset_and_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p →
    (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧
      ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  intro p F _ _ hp
  refine ⟨fun S₀ => ?_, fun S T hST h => ⟨h.1.mono hST, fun v hv => h.2 v fun a => hv (hST a)⟩⟩
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  obtain ⟨S₁, h01, h1⟩ := exists_superset_mem_sUnits F {Units.mk0 (p : F) hp0} S₀
  obtain ⟨S, h1S, hS⟩ := exists_admissible_superset_finite_places F S₁
  refine ⟨S, h01.trans h1S, hS, ?_⟩
  exact (mem_sUnits F S _).1 (h1 S h1S _ (Finset.mem_singleton_self _))

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_anisotropic_orthogonal_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModPowers
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mul_pow_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {p : ℕ} (hp : 0 < p) {y : K} (hy : y ≠ 0) :
    {a : K | a ≠ 0 ∧ ∃ r : K, a = y * r ^ p} ∈ nhds y := by
  have hd : HasStrictDerivAt (fun r : K => y * r ^ p) (y * ((p : K) * 1 ^ (p - 1))) 1 :=
    (hasStrictDerivAt_pow p (1 : K)).const_mul y
  have hne : y * ((p : K) * 1 ^ (p - 1)) ≠ 0 := by
    have : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    simp [hy, this]
  have h := hd.map_nhds_eq hne
  simp only [one_pow, mul_one] at h
  have hpow : {a : K | ∃ r : K, a = y * r ^ p} ∈ nhds y := by
    rw [← h]
    exact Filter.mem_map.2 (Filter.Eventually.of_forall fun r => ⟨r, rfl⟩)
  filter_upwards [isOpen_ne.mem_nhds hy, hpow] with a ha hb
  exact ⟨ha, hb⟩

theorem exists_approx_mod_powers :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  intro p F _ _ S y hp hy
  let U : Set (((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    ⋂ v : S, {q | q.1 v ≠ 0 ∧ ∃ r : v.1.adicCompletion F, q.1 v = y v.1 * r ^ p}
  have hU : U ∈ nhds ((fun v : S => y v.1), (0 : (F →+* ℝ) → ℝ)) := by
    refine Filter.iInter_mem.2 fun v => ?_
    have hc : Continuous fun q : ((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ) => q.1 v :=
      (continuous_apply v).comp continuous_fst
    have : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    letI : NontriviallyNormedField (v.1.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.1.adicCompletion F) ℤᵐ⁰
    exact hc.continuousAt.preimage_mem_nhds
      (mul_pow_mem_nhds (K := v.1.adicCompletion F) hp (hy v.1))
  obtain ⟨x, hx⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real F S).mem_nhds hU
  have h1 : ∀ v : S, algebraMap F (v.1.adicCompletion F) x ≠ 0 ∧
      ∃ r : v.1.adicCompletion F, algebraMap F (v.1.adicCompletion F) x = y v.1 * r ^ p :=
    fun v => Set.mem_iInter.1 hx v
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨1, one_ne_zero, fun v hv => absurd (map_zero _) (h1 ⟨v, hv⟩).1⟩
  · exact ⟨x, hx0, fun v hv => (h1 ⟨v, hv⟩).2⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCommonDenominatorNilpotentCoboundary
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory

theorem exists_denominator_of_isField_localization (B A : Type) [CommRing B] [CommRing A]
    [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] (M : Submonoid B)
    (hF : IsField (Localization M)) (f : A)
    (hf : IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) :
    ∃ m ∈ M, ∃ b' : B, algebraMap B A m * f = algebraMap B A b' := by
  letI : Field (Localization M) := hF.toField
  haveI : CharZero (Localization M) := algebraRat.charZero _
  let K := Localization M
  let A' := Localization (Algebra.algebraMapSubmonoid A M)
  haveI : IsReduced A' := inferInstance
  haveI : Algebra.FiniteType K A' := by
    haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')
    have h := RingHom.finiteType_localizationPreserves (algebraMap B A) M K A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  let g : A →ₐ[B] A' := IsScalarTower.toAlgHom B A A'
  let φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A' :=
    Algebra.TensorProduct.lift
      (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (fun _ _ => Commute.all _ _)
  have hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f) := by
    have := hf.map φ
    simpa [φ] using this
  obtain ⟨k, hk⟩ := GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn
  obtain ⟨⟨β, t⟩, ht⟩ := IsLocalization.surj M k
  have h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β) := by
    have := congrArg (algebraMap K A') ht
    rw [map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this,
      mul_comm]
    rfl
  obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1
  refine ⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩
  simpa [map_mul, mul_assoc] using hc

theorem exists_common_denominator_of_isNilpotent :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  intro B A _ _ _ _ _ _ _ hinj s hs
  classical
  haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : p.IsPrime := hp.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp⟩
    | insert a s _ ih =>
      obtain ⟨b, hb, h⟩ := ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hc, c', hc'⟩ := exists_denominator_of_isField_localization B A p.primeCompl hF a
        (hs a (Finset.mem_insert_self _ _))
      refine ⟨b * c, mul_mem hb hc, fun f hf => ?_⟩
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩
      · obtain ⟨b', hb'⟩ := h f hf
        exact ⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩
  obtain ⟨b, hb, h⟩ := key
  exact ⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_pow_eq_span_singleton (E : Type) [Field E] [NumberField E] (a : Ideal (𝓞 E))
    (ha : a ≠ ⊥) : ∃ (h : ℕ) (s : 𝓞 E), h ≠ 0 ∧ a ^ h = Ideal.span {s} := by
  have ha0 : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
  have hone : ClassGroup.mk0 ⟨a, ha0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  rw [← map_pow, SubmonoidClass.mk_pow] at hone
  have hprin : (a ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff _).mp hone
  exact ⟨Fintype.card (ClassGroup (𝓞 E)), Submodule.IsPrincipal.generator _, Fintype.card_ne_zero,
    (Ideal.span_singleton_generator _).symm⟩

theorem exists_denominator_primes_prescribed :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E) → Prop) (ι : Type) [Finite ι]
      (x : ι → E),
      (∀ i, ∀ P : HeightOneSpectrum (𝓞 E), ¬ Q P.asIdeal → P.valuation E (x i) ≤ 1) →
      ∃ s : 𝓞 E, s ≠ 0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Q P) ∧
        ∀ i, ∃ b : 𝓞 E, (s : E) * x i = (b : E) := by
  intro E _ _ Q ι _ x hx
  classical
  have : Fintype ι := Fintype.ofFinite ι

  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : E), v.valuation E y ≤ 1 →
      ∃ u : 𝓞 E, u ∉ v.asIdeal ∧ ∃ b : 𝓞 E, (u : E) * y = (b : E) := by
    intro v y hy
    obtain ⟨n, d, hnd | hnd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact hnd⟩
    · have hd : v.valuation E (algebraMap (𝓞 E) E d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        exact d.2
      have hprod : v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) = 1 := by
        rw [← map_mul, hnd, hd]
      have hn1 : 1 ≤ v.valuation E (algebraMap (𝓞 E) E n) := by
        calc (1 : _) = v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) := hprod.symm
          _ ≤ v.valuation E (algebraMap (𝓞 E) E n) := mul_le_of_le_one_left' hy
      have hn : n ∉ v.asIdeal := by
        rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
        exact le_antisymm (HeightOneSpectrum.valuation_le_one _ _) hn1
      exact ⟨n, hn, d, by rw [mul_comm]; exact hnd⟩

  let A : ι → Ideal (𝓞 E) := fun i =>
    { carrier := {r | ∃ b : 𝓞 E, (r : E) * x i = (b : E)}
      add_mem' := by
        rintro r₁ r₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
        exact ⟨b₁ + b₂, by push_cast; rw [add_mul, h₁, h₂]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c r ⟨b, h⟩
        exact ⟨c * b, by simp only [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩ }
  have memA : ∀ i r, r ∈ A i ↔ ∃ b : 𝓞 E, (r : E) * x i = (b : E) := fun _ _ => Iff.rfl
  let A0 : Ideal (𝓞 E) := ⨅ i, A i
  have hA0 : A0 ≠ ⊥ := by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) x
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    intro hbot
    apply hc0
    have hcmem : (c : 𝓞 E) ∈ A0 := by
      refine (Submodule.mem_iInf _).mpr fun i => (memA i _).mpr ?_
      obtain ⟨b, hb⟩ := hc i
      exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb.symm⟩
    rw [hbot] at hcmem
    exact (Submodule.mem_bot _).mp hcmem
  obtain ⟨h, s, hh, hs⟩ := exists_pow_eq_span_singleton E A0 hA0
  have hsA : s ∈ A0 := Ideal.pow_le_self hh (hs ▸ Ideal.mem_span_singleton_self s)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact hA0 (pow_eq_zero_iff hh |>.mp hs)
  refine ⟨s, hs0, ?_, fun i => (memA i s).mp ((Submodule.mem_iInf _).mp hsA i)⟩
  intro P hP hsP
  by_contra hQ
  have hPne : P ≠ ⊥ := fun hb => hs0 ((Submodule.mem_bot _).mp (hb ▸ hsP))
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hPne⟩
  have hle : A0 ≤ P := by
    refine hP.le_of_pow_le (n := h) ?_
    rw [hs, Ideal.span_le, Set.singleton_subset_iff]
    exact hsP
  choose u hu b hb using fun i => key v (x i) (hx i v hQ)
  have hU : (∏ i, u i) ∉ P := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu i hi
  apply hU
  refine hle ((Submodule.mem_iInf _).mpr fun i => ?_)
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) ((memA i _).mpr ⟨b i, hb i⟩)

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 → ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧ ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  first | exact @GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | exact GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | (intros; apply GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis <;> assumption)
end

