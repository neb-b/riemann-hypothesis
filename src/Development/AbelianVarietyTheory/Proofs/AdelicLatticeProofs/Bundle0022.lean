module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
section
noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.InfAdeleMixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toMixed [_root_.NumberField.IsTotallyComplex E] {R : Type} [CommRing R]
    (θ : {w : InfinitePlace E // w.IsComplex} → (R →+* ℂ)) : R →+* mixedSpace E :=
  RingHom.prod
    (Pi.ringHom fun w : {w : InfinitePlace E // w.IsReal} =>
      (False.elim (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2) : R →+* ℝ))
    (Pi.ringHom θ)

theorem mixed_ext [_root_.NumberField.IsTotallyComplex E] {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext fun w =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2).elim) (funext h)

theorem exists_place_over [_root_.NumberField.IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨⟨w, IsTotallyComplex.isComplex w⟩, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw

theorem exists_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
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
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hθ := fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)
  obtain ⟨δ, hδ0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hc' τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact hδ0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ v : InfinitePlace F, v.Completion ≃ᵢ ℝ := fun v =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v x, r v x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x :=
    fun _ _ => rfl
  let p : {w : InfinitePlace E // w.IsComplex} → InfinitePlace F := fun w =>
    InfinitePlace.mk (w.1.embedding.comp (algebraMap F E))
  let Θ : InfiniteAdeleRing F ⊗[F] E →+* mixedSpace E := toMixed fun w => θ0 w.1.embedding
  have hΘ : ∀ z w, (Θ z).2 w = θ0 w.1.embedding z := fun _ _ => rfl
  have hval : ∀ (w) (a b : InfiniteAdeleRing F), (Θ (a ⊗ₜ 1 + b ⊗ₜ δ)).2 w =
      ⟨r _ (a (p w)), r _ (b (p w)) * (w.1.embedding δ).im⟩ := by
    intro w a b
    rw [hΘ, map_add (f := _), hθ, hθ, GlobalTheory.InfAdeleCM.ext_eq_ofReal, GlobalTheory.InfAdeleCM.ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, hr, p]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, hr, p]
  choose t ht using exists_place_over (F := F) (E := E)
  have ht' : ∀ v, p (t v) = v := ht
  have htp : ∀ w, t (p w) = w := by
    intro w
    apply Subtype.ext
    rw [← InfinitePlace.mk_embedding (t (p w)).1, ← InfinitePlace.mk_embedding w.1]
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' hδ0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff (ht (p w))) with e | e
    · rw [e]
    · rw [e, InfinitePlace.mk_conjugate_eq]
  let A : (({w : InfinitePlace E // w.IsComplex}) → ℝ) → InfiniteAdeleRing F := fun y v => (r v).symm (y (t v))
  have hA : Continuous A := continuous_pi fun v => (r v).symm.continuous.comp (continuous_apply (t v))
  have hA' : ∀ y w, r _ (A y (p w)) = y w := by
    intro y w
    simp only [A, IsometryEquiv.apply_symm_apply, htp]
  let G : mixedSpace E → InfiniteAdeleRing F ⊗[F] E := fun z =>
    A (fun w => (z.2 w).re) ⊗ₜ[F] (1 : E) + A (fun w => (z.2 w).im / (w.1.embedding δ).im) ⊗ₜ[F] δ
  have hG : ∀ z, Θ (G z) = z := by
    intro z
    refine mixed_ext fun w => ?_
    rw [hval]
    refine Complex.ext (hA' (fun w => (z.2 w).re) w) ?_
    have h := hA' (fun w => (z.2 w).im / (w.1.embedding δ).im) w
    exact (congrArg (· * (w.1.embedding δ).im) h).trans (div_mul_cancel₀ _ (him _))
  have hinj : Function.Injective Θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, b, rfl⟩ := GlobalTheory.InfAdeleCM.exists_decomp hs z
    have key : ∀ v, a v = 0 ∧ b v = 0 := by
      intro v
      have h := hval (t v) a b
      rw [hz, ht' v] at h
      have h1 := congrArg Complex.re h
      have h3 := congrArg Complex.im h
      simp only [Prod.snd_zero, Pi.zero_apply, Complex.zero_re, Complex.zero_im] at h1 h3
      have z0 : r v 0 = 0 := by rw [hr, map_zero]
      exact ⟨(r v).injective (by rw [z0, ← h1]),
        (r v).injective (by rw [z0]; exact (mul_eq_zero.1 h3.symm).resolve_right (him _))⟩
    have ha : a = 0 := funext fun v => (key v).1
    have hb : b = 0 := funext fun v => (key v).2
    rw [ha, hb, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  let e : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E := RingEquiv.ofBijective Θ ⟨hinj, fun z => ⟨G z, hG z⟩⟩
  have he : ∀ z, e z = Θ z := fun _ => rfl
  have htm : ∀ x : E, Continuous fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x := by
    intro x
    have : (fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x) = fun a => a • ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.fun_smul continuous_id' continuous_const
  refine ⟨e, fun x => mixed_ext fun w => ?_, ?_, fun u hu => ?_⟩
  · rw [he, hΘ, h0, mixedEmbedding_apply_isComplex]
  · have : (e.symm : mixedSpace E → _) = G := by
      funext z
      rw [RingEquiv.symm_apply_eq, he, hG]
    rw [this]
    have c1 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).re) := by fun_prop
    have c2 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).im / (w.1.embedding δ).im) := by fun_prop
    exact Continuous.fun_add ((htm 1).comp' (hA.comp' c1)) ((htm δ).comp' (hA.comp' c2))
  · have hne : ∀ w, ((u : mixedSpace E).2 w).re ≠ 0 := by
      intro w h
      have h1 : (u : mixedSpace E).2 w = 0 := Complex.ext h (hu w)
      have h3 := congrArg (fun z : mixedSpace E => z.2 w) u.mul_inv
      simp only [Prod.snd_mul, Pi.mul_apply, h1, zero_mul, Prod.snd_one, Pi.one_apply] at h3
      exact zero_ne_one h3
    have hunit : IsUnit (A fun w => ((u : mixedSpace E).2 w).re) := by
      refine Pi.isUnit_iff.2 fun v => IsUnit.mk0 _ fun h => hne (t v) ?_
      have h1 : (r v).symm ((u : mixedSpace E).2 (t v)).re = 0 := h
      have h3 := congrArg (r v) h1
      rwa [IsometryEquiv.apply_symm_apply, hr, map_zero] at h3
    refine ⟨hunit.unit, mixed_ext fun w => ?_⟩
    have h := hval w (A fun w => ((u : mixedSpace E).2 w).re) 0
    rw [TensorProduct.zero_tmul, add_zero] at h
    rw [IsUnit.unit_spec, he, h]
    refine Complex.ext (hA' (fun w => ((u : mixedSpace E).2 w).re) w) ?_
    have z0 : r (p w) ((0 : InfiniteAdeleRing F) (p w)) = 0 := by
      rw [hr]
      exact map_zero _
    rw [hu w]
    simp only [z0, zero_mul]

end GlobalTheory.InfAdeleMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsometryMatrixRange
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isometry_matrix_range {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2

theorem ss_of_harm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ)
    (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Harm g → SS (Set.range g) := by
  intro ι _ _ σ _ τ g hτ hH W hW
  obtain ⟨H, hlog, hsum⟩ := hH
  obtain ⟨n, Q, hQ, hmem⟩ := exists_isometry_matrix_range W
  have hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N := by
    intro s
    have : ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x := fun j =>
      (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))
    choose x hx using this
    refine ⟨Matrix.of fun i j => x j i, ?_⟩
    ext i j
    have h := congrFun (hx j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  choose N hN using hN
  have hNinv : ∀ s, N (τ s) * N s = 1 := by
    intro s
    have h : Q * (N (τ s) * N s) = Q := by
      rw [← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]
    have h2 := congrArg (fun X => Qᴴ * X) h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using h2
  have hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det := by
    intro s
    have h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s := by
      calc Qᴴ * ((g s)ᴴ * g s) * Q = (g s * Q)ᴴ * (g s * Q) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (N s)ᴴ * (Qᴴ * Q) * N s := by
            rw [hN]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQ, Matrix.mul_one]
    rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha
  have hpair : ∀ s, a (τ s) + a s = 0 := by
    intro s
    have h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]
    simp only [ha]
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]
  have hasum : ∑ s, a s = 0 := by
    have h : ∑ s, (a (τ s) + a s) = 0 := Finset.sum_eq_zero fun s _ => hpair s
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ a] at h
    linarith
  have htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    simp
  have hJ := fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ
  have heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a)
      (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])
    exact fun s => h s (Finset.mem_univ s)
  have hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ := by
    intro s
    obtain ⟨M, hM⟩ := (hJ s).2 (by rw [hdet]; exact heq s)
    have h1 : N s * N (τ s) = 1 := mul_eq_one_comm.1 (hNinv s)
    have h2 : (g s)ᴴ * Q = Q * (M * N (τ s)) := by
      rw [← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    refine ⟨(M * N (τ s))ᴴ, ?_⟩
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q] at h3
  refine ⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ v hv
    obtain ⟨M, hM⟩ := hadj s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨x, rfl⟩ := (hmem v).1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at hv'
    rw [hv', Matrix.mulVec_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ,
      Matrix.one_mulVec, sub_self]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMinNormTensorOfIsClosedTensorSLOrbitStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∃ w ∈ orb d v, IsMinVec d w := by
  first | exact @GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | exact GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | (intros; apply GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
section
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory in
theorem exists_normalise_meanSquare_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov f hf hf0 hinv
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  obtain ⟨hex, h⟩ := meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov
  obtain ⟨N, hN⟩ := h f hf hinv
  refine ⟨hex, ?_⟩
  have hN0 : N ≠ 0 := by
    intro h0
    obtain ⟨μ, F, hμ, hF, h1⟩ := hex
    have h2 := (hN μ F hμ hF).2.2.1
    rw [h0, ENNReal.coe_zero, mul_zero] at h2
    have h3 : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [hF.lintegral_eq_tsum'']
      have e : ∀ (g : Γ) (x : G), ‖f (g +ᵥ x)‖ₑ = ‖f x‖ₑ := fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
      simp only [e, h2, tsum_zero]
    rw [lintegral_eq_zero_iff (hf.enorm.measurable.pow_const 2)] at h3
    apply hf0
    rw [← hf.ae_eq_iff_eq μ continuous_zero]
    filter_upwards [h3] with w hw
    simpa using hw
  have hpos : (0 : ℝ) < N := by positivity
  refine ⟨((√(N : ℝ))⁻¹ : ℝ), fun μ F hμ hF h1 => ?_⟩
  have h2 := (hN μ F hμ hF).2.2.2
  rw [h1, ENNReal.toReal_one, one_mul] at h2
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceValuationAut
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_valuation_aut (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧
      ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
  have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    exact σ.commutes (a : F)
  refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    ext a
    change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
    rw [hfix]
  · intro y
    exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y

theorem sUnits_over_and_aut : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ (τ : E ≃ₐ[F] E) (y : Eˣ), y ∈ sUnits E SE → Units.map (τ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ _ S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun σ y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := exists_place_valuation_aut F E σ w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPushoutPrimitiveRoot
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isField_tensor_of_coprime (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A]
    [Algebra F B] (h : Nat.Coprime (Module.finrank F A) (Module.finrank F B)) :
    IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B ?_
  intro K _ _ fa fb
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  have ha : Module.finrank F A = Module.finrank F fa.fieldRange :=
    (AlgEquiv.ofInjectiveField fa).toLinearEquiv.finrank_eq
  have hb : Module.finrank F B = Module.finrank F fb.fieldRange :=
    (AlgEquiv.ofInjectiveField fb).toLinearEquiv.finrank_eq
  rwa [← ha, ← hb]

theorem coprime_finrank_cyclotomic (p : ℕ) (hp : p.Prime) (F A : Type) [Field F] [Field A]
    [Algebra F A] [IsCyclotomicExtension {p} F A] : Nat.Coprime (Module.finrank F A) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite F A := IsCyclotomicExtension.finite {p} F A
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hdvd : minpoly F (IsCyclotomicExtension.zeta p F A) ∣ cyclotomic p F := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    haveI : NeZero (p : A) := hζ.neZero'
    exact (isRoot_cyclotomic_iff.mpr hζ)
  have hle := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p F)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hle
  have hfr : Module.finrank F A = (minpoly F (IsCyclotomicExtension.zeta p F A)).natDegree := by
    rw [(hζ.powerBasis F).finrank, ← (hζ.powerBasis F).natDegree_minpoly,
      IsPrimitiveRoot.powerBasis_gen]
  have hpos : 0 < Module.finrank F A := Module.finrank_pos
  have h1 := hp.pos
  exact (Nat.coprime_of_lt_prime hpos.ne' (by omega) hp).symm

theorem exists_pushout_primitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → ∃ (F' E' : Type) (_ : Field F') (_ : NumberField F') (_ : Field E') (_ : NumberField E') (_ : Algebra F F') (_ : Algebra F' E') (_ : Algebra E E') (_ : Algebra F E') (_ : IsScalarTower F F' E') (_ : IsScalarTower F E E') (ζ : F'), Algebra.IsPushout F F' E E' ∧ IsTotallyComplex F' ∧ IsGalois F' E' ∧ IsPrimitiveRoot ζ p ∧ Module.finrank F' E' = p ∧ Nat.Coprime (Module.finrank F F') p := by
  intro p F E _ _ _ _ _ _ hp h2 hdeg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : Type := CyclotomicField p F
  haveI : IsCyclotomicExtension {p} F A := CyclotomicField.isCyclotomicExtension p F
  haveI : NumberField A := IsCyclotomicExtension.numberField {p} F A
  have hco := coprime_finrank_cyclotomic p hp F A
  have hf : IsField (A ⊗[F] E) := isField_tensor_of_coprime F A E (by rwa [hdeg])
  letI : Field (A ⊗[F] E) := hf.toField
  letI : Algebra E (A ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite A (A ⊗[F] E) := inferInstance
  haveI : NumberField (A ⊗[F] E) := NumberField.of_module_finite A (A ⊗[F] E)
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hr : Module.finrank A (A ⊗[F] E) = p := by
    rw [Module.finrank_baseChange, hdeg]
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  refine ⟨A, A ⊗[F] E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsCyclotomicExtension.zeta p F A, inferInstance, ?_, ?_, hζ, hr, hco⟩
  · exact NumberField.nrRealPlaces_eq_zero_iff.mp
      (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h3 hζ)
  · apply IsGalois.of_card_aut_eq_finrank
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [Module.finrank_baseChange, ← IsGalois.card_aut_eq_finrank]
      refine Nat.card_le_card_of_injective
        (fun g : E ≃ₐ[F] E => (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) g)) ?_
      intro g h hgh
      ext x
      have := DFunLike.congr_fun hgh ((1 : A) ⊗ₜ[F] x)
      simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] at this
      exact (algebraMap E (A ⊗[F] E)).injective this

end GlobalTheory.CNorm
end

