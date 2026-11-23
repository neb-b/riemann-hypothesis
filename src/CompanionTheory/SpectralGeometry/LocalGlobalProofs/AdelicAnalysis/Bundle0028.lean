module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormInvarianceUnderUnitary
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isometry_map_ringHom {ι R S K : Type} [Fintype ι] [CommRing R] [CommRing S] [CommRing K]
    (φ : R →+* S) (α : K →+* R) (ψ : K →+* S) (hφ : ∀ x, φ (α x) = ψ x)
    (A : Matrix ι ι R) (B : Matrix ι ι K)
    (h : Aᵀ * B.map α * A = B.map α) :
    (A.map φ)ᵀ * B.map ψ * A.map φ = B.map ψ := by
  have hB : B.map ψ = (B.map α).map φ := by
    ext i j
    simp [hφ]
  have := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul] at this
  rw [hB, ← Matrix.transpose_map]
  simpa using this

theorem ginf_gfin_isometry (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (hB : ∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) *
      gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) :
    (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧
      ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω =
        B.map (algebraMap F (Af F)) := by
  refine ⟨fun ω w => ?_, fun ω => ?_⟩
  · exact isometry_map_ringHom
      ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F)))
      (algebraMap F (AF F)) (ρ w)
      (fun x => by
        have h1 : fstA F (algebraMap F (AF F) x) = algebraMap F (Ainf F) x :=
          (fstA F).commutes x
        simpa [h1] using he x w)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)
  · exact isometry_map_ringHom (sndA F : AF F →+* Af F)
      (algebraMap F (AF F)) (algebraMap F (Af F))
      (fun x => (sndA F).commutes x)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CoordMat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_one_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def traceGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

def coordL (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin M × Fin d → R) :=
  (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis R b).equivFun).trans
    (LinearEquiv.curry R R (Fin M) (Fin d)).symm

theorem coordL_apply (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    coordL R M b x p = (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := rfl

theorem trace_expand [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * inclR R e * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  have hx : ∀ z : R ⊗[F] E, z = ∑ k, (Algebra.TensorProduct.basis R b).repr z k • ((1 : R) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hs : ∀ (r : R) (w : R ⊗[F] E), sigR R σ (r • w) = r • sigR R σ w := by
    intro r w
    exact map_smul (Algebra.TensorProduct.map (AlgHom.id R R) (σ : E →ₐ[F] E)) r w
  generalize hcu : (Algebra.TensorProduct.basis R b).repr u = cu
  generalize hcv : (Algebra.TensorProduct.basis R b).repr v = cv
  have hu : u = ∑ k, cu k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcu]; exact hx u
  have hv : v = ∑ k, cv k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcv]; exact hx v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu, hv, map_sum, Finset.sum_mul, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : sigR R σ ((1 : R) ⊗ₜ[F] b k) = (1 : R) ⊗ₜ[F] σ (b k) := by simp [sigR]
  have h2 : inclR R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [hs, h1, h2, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    trace_one_tmul, smul_eq_mul, smul_eq_mul]
  ring

theorem trace_hR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      coordL R M b x ⬝ᵥ (traceGram σ J b).map (algebraMap F R) *ᵥ coordL R M b y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, JR, Matrix.map_apply, trace_expand R σ b]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, coordL_apply, traceGram, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hform_mulVec {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J g : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  have h : ∀ (K : Matrix (Fin M) (Fin M) A) (u v : Fin M → A), hform s K u v = (s ∘ u) ⬝ᵥ (K *ᵥ v) := by
    intro K u v
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : s ∘ (g *ᵥ x) = (g.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [h, h, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp only [cT, Matrix.mul_assoc]

theorem matrix_ext_dot {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A] (P Q : Matrix ι ι A)
    (h : ∀ u v : ι → A, u ⬝ᵥ P *ᵥ v = u ⬝ᵥ Q *ᵥ v) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

theorem dot_conj {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by
  rw [← Matrix.vecMul_transpose g u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem traceGram_isSymm [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  refine Matrix.IsSymm.ext fun p q => ?_
  simp only [traceGram]
  have hm : e (σ (b q.2) * J q.1 p.1 * b p.2) = σ (b p.2) * J p.1 q.1 * b q.2 := by
    change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
    rw [map_mul, map_mul, hσ, hJ]
    ring
  exact (Algebra.trace_eq_of_algEquiv e _).symm.trans (congrArg _ hm)

theorem traceGram_det_ne_zero [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (b : Module.Basis (Fin d) F E) : (traceGram σ J b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  let y : Fin M → E := fun j => ∑ l, v (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, traceGram, Pi.zero_apply] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have h2 : ∀ i z, Algebra.trace F E (z * (J *ᵥ y) i) = 0 := by
    intro i z
    have hz : z = ∑ k, b.repr (σ z) k • σ (b k) := by
      have h := congrArg σ (b.sum_repr (σ z))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hσ, map_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun k _ => map_smul σ _ _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, h1, smul_zero]
  have h3 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact h2 i z
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hJ h3
  funext p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun l => v (p.1, l)) (congrFun h4 p.1) p.2

theorem hR_mat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hm : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
  rw [hR, hform_mulVec, hm, hR]

end Alg

theorem coord_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (h : HA R σ J), ∃ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ X : Fin 1 → Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2 := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  refine ⟨traceGram σ J b, traceGram_isSymm σ hσ J hJ.1 b, traceGram_det_ne_zero σ hσ J hJ.2 b,
    fun R _ _ h => ?_⟩
  let c := coordL (F := F) (E := E) R M b
  let T : (Fin M → R ⊗[F] E) →ₗ[R] (Fin M → R ⊗[F] E) :=
    (Matrix.mulVecLin (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))).restrictScalars R
  let g : Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
    LinearMap.toMatrix' (c.toLinearMap ∘ₗ T ∘ₗ c.symm.toLinearMap)
  have hg : ∀ x, g *ᵥ c x = c ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) := by
    intro x
    simp [g, T, LinearMap.toMatrix'_mulVec]
  refine ⟨g, ?_, fun X => (hg (X 0)).symm⟩
  refine matrix_ext_dot _ _ fun u v => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  obtain ⟨y, rfl⟩ := c.surjective v
  rw [dot_conj, hg, hg]
  have hx := trace_hR R σ J b x y
  have hy := trace_hR R σ J b ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
  rw [hR_mat] at hy
  exact hy.symm.trans hx

end GlobalTheory.CompanionTheory.SW.CoordMat
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitChoiceOfIsArtinianRingIsReduced
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    apply congrArg φ.symm
    funext I
    by_cases h : c I = i <;> simp [Pi.mul_apply, E, h]
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    apply congrArg φ.symm
    funext I
    by_cases hi : c I = i
    · simp [Pi.mul_apply, E, hi, hij]
    · simp [Pi.mul_apply, E, hi]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, ← map_one φ.symm]
      apply congrArg φ.symm
      funext I
      simp [Finset.sum_apply, E]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
      intro I
      have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
        simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
          one_mul, zero_mul, Fintype.sum_ite_eq]
      rw [hcomp]
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      letI := Ideal.Quotient.field I.asIdeal
      exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HInv

theorem det_mul_conj_eq_one {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]
    (τ : A →+* A) (g J : Matrix m m A) (hg : cT τ g * J * g = J) (hJ : IsUnit J.det) :
    g.det * τ g.det = 1 := by
  have hc : (cT τ g).det = τ g.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hc] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem map_tuple_eq {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (τ : K →+* K) (hc : Continuous τ)
    (hi : ∀ y, τ (τ y) = y) {M n : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (hA : A.det * τ A.det = 1) (μ : Measure (Fin n → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (fun X a => A *ᵥ X a) = μ := by
  let lam : Measure K := Measure.addHaar
  have hl : lam.map (fun y => A.det * y) = lam :=
    NormOneHaar.map_mul_eq_of_norm_one K τ hc hi lam _ hA
  let μ0 : Measure (Fin M → K) := Measure.pi fun _ => lam
  have hdet : IsUnit A.det := IsUnit.of_mul_eq_one _ hA
  have h0 : μ0.map (fun x => A *ᵥ x) = μ0 := by
    have := ModDet.map_mulVec_eq_smul K (Fin M) μ0 lam A hdet 1 (by simpa using hl)
    simpa using this
  let P : Measure (Fin n → Fin M → K) := Measure.pi fun _ => μ0
  have hmeas : Measurable (fun x : Fin M → K => A *ᵥ x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI hs : SigmaFinite (μ0.map (fun x => A *ᵥ x)) := by
    rw [h0]; infer_instance
  have hP : P.map (fun X a => A *ᵥ X a) = P := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => μ0) (f := fun _ x => A *ᵥ x)
      (fun _ => hmeas.aemeasurable)
    simpa only [h0] using this
  have e := Measure.isAddLeftInvariant_eq_smul μ P
  have htuple : Measurable (fun (X : Fin n → Fin M → K) a => A *ᵥ X a) :=
    Measurable.of_eval fun a => hmeas.comp (measurable_pi_apply a)
  rw [e, Measure.map_smul _ htuple.aemeasurable, hP]

theorem map_actW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
    IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure →
    ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ hμ h
  obtain ⟨r1, r2, r3, r4, r5, r6, -, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI := r5
  haveI := r6
  obtain ⟨t1, t2, t3, t4, tc, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨a1, a2, -, ai, -⟩ := KAlg.algebra_tensor_invol F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := a1
  haveI := a2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, JR]
    rw [e]
    exact (IsUnit.mk0 _ hJ.2).map (inclR (F := F) R)
  have hg : cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR (F := F) R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R J :=
    (show (h : HR R σ J).1 ∈ HR R σ J from (h : HR R σ J).2)
  exact map_tuple_eq (sigR R σ) tc ai _ (det_mul_conj_eq_one _ _ _ hg hJu) μ

end GlobalTheory.CompanionTheory.SW.HInv
end

