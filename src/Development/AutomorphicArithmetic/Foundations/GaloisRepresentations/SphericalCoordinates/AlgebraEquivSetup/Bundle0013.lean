module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private lemma exists_int_multiple (x : Matrix (Fin n) (Fin n) E) :
    ∃ (m : ℤ) (y : Matrix (Fin n) (Fin n) (𝓞 E)), m ≠ 0 ∧ y.map (algebraMap (𝓞 E) E) = (m : ℚ) • x := by
  classical
  obtain ⟨m, hm, hs⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun ij : Fin n × Fin n => x ij.1 ij.2))
  have h : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (m : ℚ) • x i j := by
    intro i j
    have h1 := hs (x i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2 : m • x i j = (m : ℚ) • x i j := by
      simp [zsmul_eq_mul, Algebra.smul_def]
    rw [h2] at h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h1, IsIntegralClosure.algebraMap_mk' _ _ _⟩
  choose y hy using h
  refine ⟨m, Matrix.of y, hm, ?_⟩
  ext i j
  simp [hy]

private lemma beta_rep (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (hrep : ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
      rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) : β (rep x z) = x *ᵥ β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
  | tmul q v =>
    have hq : q ⊗ₜ[ℤ] v = q • ((1 : ℚ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul']; simp
    obtain ⟨m, y, hm, hy⟩ := exists_int_multiple x
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have key : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) := by
      have e1 : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = β (rep ((m : ℚ) • x) (1 ⊗ₜ v)) := by
        rw [map_smul, LinearMap.smul_apply, map_smul]
      have e2 : (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) = ((m : ℚ) • x) *ᵥ β (1 ⊗ₜ v) := by
        rw [smul_mulVec]
      rw [e1, e2, ← hy, hrep]
      ext i
      rw [hβ]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [show ((∑ k, y i k * v k : 𝓞 E) : E) = ∑ k, ((y i k : 𝓞 E) : E) * (v k : E) by
        simp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ]
    have h3 : β (rep x (1 ⊗ₜ v)) = x *ᵥ β (1 ⊗ₜ v) := smul_right_injective _ hmq key
    rw [hq, map_smul, map_smul, map_smul, mulVec_smul, h3]

private def nu (R : Type) [CommRing R] [Algebra ℚ R] (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) :
    R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) ≃+ (Fin n → R ⊗[ℚ] E) :=
  ((TensorProduct.congr (LinearEquiv.refl ℚ R) β).trans
    (TensorProduct.piRight ℚ ℚ R (fun _ : Fin n => E))).toAddEquiv

private lemma nu_tmul (R : Type) [CommRing R] [Algebra ℚ R]
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) (r : R) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) (i : Fin n) :
    nu R β (r ⊗ₜ z) i = r ⊗ₜ (β z i) := by
  simp [nu]

private lemma actOn_tmul {R : Type} [CommRing R] [Algebra ℚ R]
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (r r' : R) (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    actOn rep R (r ⊗ₜ x) (r' ⊗ₜ z) = (r * r') ⊗ₜ rep x z := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  show r • (LinearMap.baseChange R (rep x)) (r' ⊗ₜ z) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private lemma nu_act {R : Type} [CommRing R] [Algebra ℚ R]
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hr : ∀ x z, β (rep x z) = x *ᵥ β z)
    (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (v : R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    nu R β (actOn rep R y v) = μ y *ᵥ nu R β v := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, add_mulVec, ha, hb]
  | tmul r x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
    | tmul r' z =>
      ext1 i
      rw [actOn_tmul, nu_tmul, hr]
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hμ r x i k, nu_tmul, Algebra.TensorProduct.tmul_mul_tmul]

private lemma nu_mem {p : ℕ} (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (v : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    v ∈ AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
        ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} ↔
      ∀ i, nu (AfP p) β v i ∈ OHat p E := by
  classical
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, x i, ha, by rw [nu_tmul, hβ]⟩
    | zero => simpa using zero_mem _
    | add a b _ _ h1 h2 =>
      simpa only [map_add, Pi.add_apply] using add_mem h1 h2
    | neg a _ h => rw [map_neg]; exact neg_mem h
  · intro h
    have hs : ∀ i, ∀ w ∈ OHat p E, (nu (AfP p) β).symm (Pi.single i w) ∈
        AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
          ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} := by
      intro i w hw
      induction hw using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, x, ha, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, Pi.single i x, ha, ?_⟩
        rw [AddEquiv.symm_apply_eq]
        funext j
        rw [nu_tmul, hβ]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      | zero => simpa using zero_mem _
      | add a b _ _ h1 h2 => rw [Pi.single_add, map_add (f := _)]; exact add_mem h1 h2
      | neg a _ h => rw [Pi.single_neg, map_neg]; exact neg_mem h
    have hv : v = ∑ i, (nu (AfP p) β).symm (Pi.single i (nu (AfP p) β v i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]; simp
    rw [hv]
    exact sum_mem fun i _ => hs i _ (h i)

end UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

namespace UpperTheory.Gal.W2.Seed

open LatticeTensorCoordinates

theorem pLatCoord :
    RepLaws → LatCoord := by
  intro _ E _ _ _ A n p _ S μ hμ
  obtain ⟨β, hβ⟩ := pRepEx E n
  have hr : ∀ x z, β (S.L.rep x z) = x *ᵥ β z := beta_rep S.L.rep S.L_rep β hβ
  refine ⟨nu (AfP p) β, ?_, ?_, ?_⟩
  · intro r v i
    exact (nu_tmul (AfP p) β r _ i).trans (congrArg (fun t => r ⊗ₜ[ℚ] t) (hβ v i))
  · intro h v
    exact nu_act μ hμ S.L.rep β hr (S.mx h) v
  · intro v
    exact nu_mem β hβ v

end UpperTheory.Gal.W2.Seed
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} [Fact p.Prime]

private theorem conj_dg (A : Arith E) (n : ℕ) (i : Fin n) :
    IsCMField.complexConj E (A.dg n i : E) = (A.dg n i : E) := by
  rw [← A.bar_eq]
  unfold Arith.dg
  split_ifs <;> simp [A.c_real]

private abbrev Dg (A : Arith E) (n : ℕ) : Matrix (Fin n) (Fin n) E := Matrix.diagonal fun i => (A.dg n i : E)

private theorem H_eq (A : Arith E) (n : ℕ) : A.H n = (-(A.c : E)) • Dg A n := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Arith.H, Arith.hd]
  · simp [Arith.H, h]

private theorem Dg_map (A : Arith E) (n : ℕ) : (Dg A n).map (IsCMField.complexConj E : E →+* E) = Dg A n := by
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1; funext i
  exact conj_dg A n i

private theorem H_map (A : Arith E) (n : ℕ) : (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have h := A.herm n
  have h2 : (A.H n)ᵀ = A.H n := by unfold Arith.H; simp
  have h3 := congrArg Matrix.transpose h
  rw [Matrix.transpose_transpose, h2] at h3
  exact h3

private theorem c_ne' (A : Arith E) : -(A.c : E) ≠ 0 := neg_ne_zero.2 A.c_ne

private theorem Dg_star (A : Arith E) (n : ℕ) (x : Matrix (Fin n) (Fin n) E) :
    Dg A n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * Dg A n := by
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have h1 : A.H n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * A.H n := by
    rw [hermStar_apply, H_map]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  generalize (hermStar (A.H n) (A.det_ne n) x).unop = Y at h1 ⊢
  rw [H_eq A n, Matrix.smul_mul, Matrix.mul_smul] at h1
  exact smul_right_injective _ (c_ne' A) h1

private theorem baseMatrix_eq_diagonal (A : Arith E) (n : ℕ) : ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) = Dg A n := rfl

private theorem hermStar_baseMatrix (A : Arith E) (n : ℕ) :
    (hermStar (A.H n) (A.det_ne n) ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)).unop = A.β₀ n := by
  apply (Units.mul_right_inj (A.β₀ n)).1
  rw [baseMatrix_eq_diagonal, Dg_star, Dg_map]
  simp

private theorem sim_of (A : Arith E) (n : ℕ) (y : (Matrix (Fin n) (Fin n) E)ˣ) (s : ℚˣ)
    (h : (y : Matrix (Fin n) (Fin n) E) * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) *
      (hermStar (A.H n) (A.det_ne n) y).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ)) :
    ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E : E →+* E))ᵀ * (y : Matrix (Fin n) (Fin n) E) =
      algebraMap ℚ E s • (1 : Matrix (Fin n) (Fin n) E) := by
  have hs : algebraMap ℚ E (s : ℚ) ≠ 0 := (map_ne_zero _).2 s.ne_zero
  refine (mul_eq_smul_one_comm hs).1 ?_
  rw [Matrix.mul_assoc, baseMatrix_eq_diagonal, Dg_star, ← Matrix.mul_assoc, ← baseMatrix_eq_diagonal] at h
  have h2 := (Units.mul_left_inj (A.β₀ n)).1 h
  rw [h2]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

private theorem gram_psi (A : Arith E) (n : ℕ) (τ : E →+* ℂ) (b : Matrix (Fin n) (Fin n) E) (hb : Dg A n * b = 1) :
    gramAt (A.H n) τ * b.map τ = (-τ (A.c : E)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e1 : gramAt (A.H n) τ = (-τ (A.c : E)) • (Dg A n).map τ := by
    ext i j
    by_cases h : i = j
    · subst h; simp [gramAt, Arith.H, Arith.hd]
    · simp [gramAt, Arith.H, h, Ne.symm h]
  have e2 : (Dg A n).map τ * b.map τ = 1 := by
    rw [← Matrix.map_mul, hb, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e1, Matrix.smul_mul, e2]

private theorem c_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.c : E)).im = 0 := by
  have h1 : τ (IsCMField.complexConj E (A.c : E)) = (starRingEnd ℂ) (τ (A.c : E)) :=
    IsCMField.complexEmbedding_complexConj E τ _
  rw [← A.bar_eq, A.c_real] at h1
  exact Complex.conj_eq_iff_im.1 h1.symm

private theorem form_val (r : ℂ) (hr : r.im = 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (star x ⬝ᵥ ((r • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x)).re = r.re * t := by
  open scoped ComplexOrder in
  have h := Matrix.dotProduct_star_self_pos_iff.2 hx
  refine ⟨(star x ⬝ᵥ x).re, (Complex.pos_iff.1 h).1, ?_⟩
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, hr, zero_mul, sub_zero]

private theorem c_neg_of (A : Arith E) (τ : E →+* ℂ) (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) :
    (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · rw [h]; exact A.c_neg
  · have := A.c_neg
    rw [← h] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

private theorem book_constants_pos_of_pos (A : Arith E) (n : ℕ) (hs : A.SigOK n) (v : InfinitePlace E) (b : Matrix (Fin n) (Fin n) E)
    (hb : Dg A n * b = 1) (x : Fin n → ℂ) (hx : x ≠ 0) :
    (sigPos (A.herm n) v.embedding = 1 → 0 < (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re) ∧
    (sigPos (A.herm n) v.embedding ≠ 1 → (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re < 0) := by
  rw [gram_psi A n _ b hb]
  obtain ⟨t, ht, he⟩ := form_val (-v.embedding (A.c : E)) (by simp [c_im]) x hx
  rw [he]
  have hm : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
  constructor
  · intro h1
    have hv : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀ := by
      by_contra hne
      have := ((hs v.embedding).2 hne).1
      omega
    have := c_neg_of A _ hv
    simp only [Complex.neg_re]
    nlinarith
  · intro h1
    have hv : InfinitePlace.mk v.embedding ≠ InfinitePlace.mk A.τ₀ := fun h => h1 ((hs v.embedding).1 h).1
    have := A.c_pos _ hv
    simp only [Complex.neg_re]
    nlinarith

variable {A : Arith E}

private theorem iso_map {S : Setup A n p} (T : Tr S) :
    ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ * Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) * T.a.val.map T.Φ = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Af E) => M.map T.Φ) T.iso.1
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  have e1 : ((T.a.val.map (conjFin (conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
    ext i j
    exact T.Φ_conj _
  have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1; funext i
    exact T.Φ_E _
  rw [e1, e2] at h
  exact h

private def xU {S : Setup A n p} (T : Tr S) : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ :=
  Units.map (T.μ.symm : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E) →* AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
    (GeneralLinearGroup.map T.Φ T.a)

private theorem traceMap_unipotent {S : Setup A n p} (T : Tr S) : T.μ (xU T) = T.a.val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

private theorem mu_xi {S : Setup A n p} (T : Tr S) : T.μ ((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) = (T.a⁻¹).val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

private theorem mu_b {S : Setup A n p} (T : Tr S) (y : Matrix (Fin n) (Fin n) E) :
    T.μ ((1 : AfP p) ⊗ₜ[ℚ] y) = y.map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.mu 1 y i k

private theorem triv_mat (hM : MuStar) {S : Setup A n p} (T : Tr S) :
    (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] Dg A n) *
      (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xU T)).unop = 1 := by
  apply T.μ.injective
  have h := hM (AfP p) E A n T.μ T.mu (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
  have h0 := iso_map T
  rw [map_mul, map_mul, map_one, mu_b, traceMap_unipotent, Matrix.mul_assoc]
  rw [traceMap_unipotent] at h
  have e : (Dg A n).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (by simp)]
  rw [e, h]
  exact mul_eq_one_comm.1 h0

private def similitudeToGammaZeroHom (S : Setup A n p) : GlobalTheory.LKCx.grp S.G (A.β₀ n) →* Gam0 E n where
  toFun y := ⟨y.1, Subgroup.mem_inf.2 ⟨sim_of A n y.1.1 y.1.2 y.2.1, y.2.2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem mat_rat {S : Setup A n p} (T : Tr S) (y : Gam0 E n) :
    (mat (rat y)).val.map T.Φ = (y.1.1.val).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.Φ_E _

private theorem rho_rat {S : Setup A n p} (T : Tr S) (s : ℚ) : T.ρ (algebraMap ℚ AfQ s) = algebraMap ℚ (AfP p) s :=
  RingHom.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) s

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pStdForm :
    MuStar → StdForm := by
  intro hM E _ _ _ A n p _ S T
  let β : S.G.Cˣ := A.β₀ n
  have hx : Triv S.G (AfP p) (β : S.G.C) (xU T) 1 :=
    (triv_mat hM T).trans (map_one (algebraMap (AfP p) (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E))).symm
  have hsym : sh S.G (β : S.G.C) = (β : S.G.C) := hermStar_baseMatrix A n
  let B : DForm S.G := ⟨β, hsym, ⟨xU T, 1, hx⟩, fun v x h0 =>
    book_constants_pos_of_pos A n S.sig v (((A.β₀ n)⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) (Units.mul_inv (A.β₀ n)) x h0⟩
  refine ⟨B, xU T, hx, similitudeToGammaZeroHom S, fun y => rfl, fun y => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply T.μ.injective
    have h1 := T.j_mx (rat (similitudeToGammaZeroHom S y))
    let Y : (Matrix (Fin n) (Fin n) E)ˣ := y.1.1
    have h2 : T.μ (S.mx (GlobalTheory.LKCx.toAfF S.G B.β (xU T) 1 hx y)) =
        T.a.val.map T.Φ * (Y : Matrix (Fin n) (Fin n) E).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) * (T.a⁻¹).val.map T.Φ := by
      show T.μ ((xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] (Y : Matrix (Fin n) (Fin n) E)) *
        (((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)) = _
      rw [map_mul, map_mul, traceMap_unipotent, mu_xi, mu_b]
    refine h2.trans (Eq.trans ?_ h1.symm)
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, mat_rat]
    rfl
  · apply Units.ext
    have h1 := T.j_sim (rat (similitudeToGammaZeroHom S y))
    exact (rho_rat T _).symm.trans h1.symm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.UptsExt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem upts_ext {C : Type} [Ring C] [Algebra ℚ C] [Nontrivial C] {star : C →+* Cᵐᵒᵖ} {R : Type} [CommRing R] [Algebra ℚ R]
    (x y : UPts star R) (h : (((x : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) = ((y : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ)) :
    x = y := by
  obtain ⟨⟨g, c⟩, hx⟩ := x
  obtain ⟨⟨g', c'⟩, hy⟩ := y
  have hx' : (g : R ⊗[ℚ] C) * (starT star R g).unop = algebraMap R (R ⊗[ℚ] C) c := hx
  have hy' : (g' : R ⊗[ℚ] C) * (starT star R g').unop = algebraMap R (R ⊗[ℚ] C) c' := hy
  have hg : g = g' := Units.ext h
  subst hg
  have hinj : Function.Injective (algebraMap R (R ⊗[ℚ] C)) := fun a b hab =>
    Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R) (B := C) (algebraMap ℚ C).injective hab
  have hc : c = c' := Units.ext (hinj (hx'.symm.trans hy'))
  subst hc
  rfl

theorem UpperTheory.Gal.W2.Seed.pTrEx :
    AdTEx → MuEx → IsoEx' → JEx → JEq → JSurj → TrEx := by
  intro hT hM hI hJ hQ hS E _ _ _ A n p _ S hn
  obtain ⟨T⟩ := hT p E
  obtain ⟨μ, hμ⟩ := hM (AfP p) E n
  obtain ⟨a, ha⟩ := hI E A n hn
  obtain ⟨j, hj1, hj2⟩ := hJ E A n p S T μ hμ a ha
  obtain ⟨hc, he⟩ := hQ E A n p S T μ hμ a j hj1
  choose sec hs1 hs2 using hS E A n p S T μ hμ a ha
  have hjs : ∀ h, j (sec h) = h := fun h =>
    upts_ext _ _ (μ.injective ((hj1 (sec h)).trans (hs1 h).symm))
  have hmul : ∀ h h', sec (h * h') = sec h * sec h' := by
    intro h h'
    apply hc
    intro w
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, hs2 _ w hw, hs2 _ w hw, hs2 _ w hw, one_mul]
    · exact (he _ _).1 (by rw [map_mul, hjs, hjs, hjs]) w hw
  exact ⟨{ T with
    μ := μ, mu := hμ, a := a, iso := ha, j := j, j_mx := hj1, j_sim := hj2
    sec := MonoidHom.mk' sec hmul, j_sec := hjs, sec_p := hs2, j_eq := he }⟩
end

