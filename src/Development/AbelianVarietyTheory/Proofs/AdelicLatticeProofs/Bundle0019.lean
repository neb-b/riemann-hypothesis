module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicUnitaryScalingUnit
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem finite_det_one_add_smul_eq_zero {E K : Type} [Field E] [Field K] (φ : E →+* K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : {l : E | (1 + φ l • G).det = 0}.Finite := by
  let p : Polynomial K := (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C).det
  have hp : ∀ x : K, p.eval x = (1 + x • G).det := by
    intro x
    have := (Polynomial.evalRingHom x).map_det (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 0
    rw [h] at this
    simp at this
  have hfin : (p.rootSet K).Finite := p.rootSet_finite K
  refine (hfin.preimage φ.injective.injOn).subset fun l hl => ?_
  simp only [Set.mem_preimage, Polynomial.mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hp]
  exact hl

theorem finite_not_isUnit_det {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (ε : R) (hε : ε * ε = ε)
    (hfin : {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}.Finite) :
    {l : E | ¬ IsUnit (1 + φ l • (ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R))).det}.Finite := by
  set G := ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) with hG
  have key : ∀ (M : Ideal R) (l : E), Ideal.Quotient.mk M (1 + φ l • G).det =
      (1 + ((Ideal.Quotient.mk M).comp φ) l • G.map (Ideal.Quotient.mk M)).det := by
    intro M l
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : ∀ M ∈ {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}, {l : E | (1 + φ l • G).det ∈ M}.Finite := by
    rintro M ⟨hM, -⟩
    letI := Ideal.Quotient.field M
    refine (finite_det_one_add_smul_eq_zero ((Ideal.Quotient.mk M).comp φ)
      (G.map (Ideal.Quotient.mk M))).subset fun l hl => ?_
    rw [Set.mem_setOf_eq, ← key, Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  refine ((hfin.biUnion h1).union (Set.finite_singleton (-1))).subset fun l hl => ?_
  obtain ⟨M, hM, hl⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hl)
  have h0 : ε * (1 - ε) ∈ M := by
    rw [mul_sub, mul_one, hε, sub_self]; exact M.zero_mem
  rcases hM.isPrime.mem_or_mem h0 with h | h
  · right
    letI := Ideal.Quotient.field M
    have h2 := Ideal.Quotient.eq_zero_iff_mem.2 hl
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2 h
    have h4 : G.map (Ideal.Quotient.mk M) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hG, hij, Matrix.one_apply, h3]
    rw [key, h4] at h2
    have h5 : (1 + ((Ideal.Quotient.mk M).comp φ) l • (1 : Matrix (Fin n) (Fin n) (R ⧸ M))) =
        ((Ideal.Quotient.mk M).comp φ) (1 + l) • 1 := by
      rw [map_add (f := _), map_one, add_smul, one_smul]
    rw [h5, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    have h6 := (map_eq_zero _).1 (pow_eq_zero_iff (by
      intro h; rw [h] at h2; simp at h2) |>.1 h2)
    exact eq_neg_of_add_eq_zero_right h6
  · left
    exact Set.mem_biUnion (s := {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}) ⟨hM, h⟩ hl

noncomputable def adEval (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v

theorem adEval_surjective (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (adEval F v) := by
  classical
  intro x
  refine ⟨⟨Pi.single v x, ?_⟩, ?_⟩
  · filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _
  · exact Pi.single_eq_same v x

theorem finite_primes_one_sub (F : Type) [Field F] [NumberField F] (e : FiniteAdeleRing (𝓞 F) F)
    (he : {v | e v ≠ 0}.Finite) :
    {P : Ideal (FiniteAdeleRing (𝓞 F) F) | P.IsPrime ∧ 1 - e ∈ P}.Finite := by
  refine (he.image fun v => RingHom.ker (adEval F v)).subset ?_
  rintro P ⟨hP, h⟩
  have hle : he.toFinset.inf (fun v => RingHom.ker (adEval F v)) ≤ P := by
    intro a ha
    have h0 : a * e = 0 := by
      refine FiniteAdeleRing.ext F fun v => ?_
      change a v * e v = 0
      by_cases hv : e v = 0
      · rw [hv, mul_zero]
      · have h1 : a ∈ RingHom.ker (adEval F v) :=
          (Finset.inf_le (f := fun v => RingHom.ker (adEval F v)) (he.mem_toFinset.2 hv)) ha
        have h2 : a v = 0 := h1
        rw [h2, zero_mul]
    have : a = a * (1 - e) := by rw [mul_sub, h0, mul_one, sub_zero]
    rw [this]
    exact P.mul_mem_left _ h
  obtain ⟨v, hv, hvP⟩ := (Ideal.IsPrime.inf_le' hP).1 hle
  exact ⟨v, he.mem_toFinset.1 hv,
    (RingHom.ker_isMaximal_of_surjective _ (adEval_surjective F v)).eq_of_le hP.ne_top hvP⟩

theorem infinite_norm_one {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) : {l : E | l * c l = 1}.Infinite := by
  first
  | exact @_root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | (apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite ..)

theorem exists_norm_one_isUnit_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  intro F E _ _ _ _ _ c hrk hc hc1 n g e he hfin
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  have hM : {M : Ideal (RA F E) | M.IsMaximal ∧ 1 - e ⊗ₜ[F] (1 : E) ∈ M}.Finite := by
    refine ((finite_primes_one_sub F e hfin).biUnion fun P _ =>
      Algebra.QuasiFinite.finite_primesOver (S := RA F E) P).subset ?_
    rintro M ⟨hM, h⟩
    haveI := hM.isPrime
    refine Set.mem_biUnion (x := M.under (FiniteAdeleRing (𝓞 F) F)) ⟨inferInstance, ?_⟩
      ⟨inferInstance, inferInstance⟩
    rw [← hsub] at h
    exact h
  have hbad := finite_not_isUnit_det
    (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom g (e ⊗ₜ[F] (1 : E))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, he, mul_one]) hM
  obtain ⟨l, hl, hl'⟩ := (infinite_norm_one c hc hc1).exists_notMem_finite hbad
  refine ⟨l, hl, ?_⟩
  rw [hsub]
  exact not_not.1 hl'

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates (F E K : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E) :
    algebraMap K (K ⊗[F] E) (Algebra.norm K y) =
      ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  classical
  set G := E ≃ₐ[F] E
  have hcard : Fintype.card G = Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E, Nat.card_eq_fintype_card]
  let b : Module.Basis G F E := (Module.finBasis F E).reindex (Fintype.equivFinOfCardEq hcard).symm
  let b' : Module.Basis G K (K ⊗[F] E) := Algebra.TensorProduct.basis K b
  set A := Algebra.leftMulMatrix b' y with hA
  let P : Matrix G G E := fun g j => g (b j)
  have hP : P.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    have hj : ∀ j, ∑ g, v g * g (b j) = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct, P] using congrFun hv j
    have hx : ∀ x : E, ∑ g, v g * g x = 0 := fun x => by
      calc ∑ g, v g * g x = ∑ g, v g * g (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr x j • ∑ g, v g * g (b j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => by rw [AlgEquiv.commutes]; ring
        _ = 0 := by simp [hj]
    have hli := (linearIndependent_monoidHom E E).comp
      (fun g : G => (g : E ≃* E).toMonoidHom) (fun g₁ g₂ h => by
        ext x; exact DFunLike.congr_fun h x)
    have := Fintype.linearIndependent_iff.mp hli v (by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact hx x)
    exact hv0 (funext this)
  let P' : Matrix G G (K ⊗[F] E) := P.map Algebra.TensorProduct.includeRight
  have key : Matrix.diagonal
      (fun g : G => Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y) * P'
      = P' * A.map (algebraMap K (K ⊗[F] E)) := by
    ext g j
    have h1 : y * b' j = ∑ i, A i j • b' i := by
      simpa [A, Algebra.leftMulMatrix_eq_repr_mul] using (b'.sum_repr (y * b' j)).symm
    have h2 := congrArg (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, b', Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.smul_def,
      AlgHom.commutes] at h2
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    change _ * (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b j)) =
      ∑ i, (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b i)) * algebraMap K (K ⊗[F] E) (A i j)
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet := congrArg Matrix.det key
  have hAdet : (A.map (algebraMap K (K ⊗[F] E))).det = algebraMap K (K ⊗[F] E) A.det :=
    (RingHom.map_det _ _).symm
  have hPdet : P'.det = Algebra.TensorProduct.includeRight P.det :=
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hAdet, hA,
    ← Algebra.norm_eq_matrix_det] at hdet
  have hu : IsUnit P'.det := by
    rw [hPdet]; exact (isUnit_iff_ne_zero.mpr hP).map _
  exact (hu.mul_left_cancel (by rw [mul_comm]; exact hdet)).symm

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BorelHarishChandra
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.SiegelBound

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : Type}

def Bdd (F : T → Matrix ι ι ℂ) : Prop := ∃ C : ℝ, ∀ t i j, ‖F t i j‖ ≤ C

omit [DecidableEq ι] in
theorem Bdd.cont {F : T → Matrix ι ι ℂ} (hF : Bdd F) {f : Matrix ι ι ℂ → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ t, f (F t) ≤ C := by
  obtain ⟨C, hC⟩ := hF
  have hK : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hK.bddAbove_image (f := f) hf.continuousOn
  refine ⟨B, fun t => hB ⟨F t, fun i _ j _ => ?_, rfl⟩⟩
  simpa using hC t i j

omit [DecidableEq ι] in
theorem Bdd.comp {F : T → Matrix ι ι ℂ} (hF : Bdd F) {f : Matrix ι ι ℂ → Matrix ι ι ℂ} (hf : Continuous f) :
    Bdd fun t => f (F t) := by
  obtain ⟨C, hC⟩ := hF.cont (f := fun y => ∑ i, ∑ j, ‖f y i j‖) (by fun_prop)
  refine ⟨C, fun t i j => le_trans ?_ (hC t)⟩
  calc ‖f (F t) i j‖ ≤ ∑ j, ‖f (F t) i j‖ :=
        Finset.single_le_sum (f := fun j => ‖f (F t) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖f (F t) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem Bdd.mul {F G : T → Matrix ι ι ℂ} (hF : Bdd F) (hG : Bdd G) : Bdd fun t => F t * G t := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  refine ⟨∑ _k : ι, C * D, fun t i j => ?_⟩
  beta_reduce
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC t i k) (hD t k j) (norm_nonneg _) ((norm_nonneg _).trans (hC t i k))

theorem Bdd.adj {F : T → Matrix ι ι ℂ} (hF : Bdd F) : Bdd fun t => (F t).adjugate :=
  hF.comp (f := fun y => y.adjugate) (continuous_id.matrix_adjugate)

omit [DecidableEq ι] in
theorem Bdd.ct {F : T → Matrix ι ι ℂ} (hF : Bdd F) : Bdd fun t => (F t)ᴴ :=
  hF.comp (f := fun y => yᴴ) (continuous_id.matrix_conjTranspose)

theorem bdd_unitary {F : T → Matrix ι ι ℂ} (hF : ∀ t, (F t)ᴴ * F t = 1) : Bdd F :=
  ⟨1, fun t i j => entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (hF t)) i j⟩

theorem Bdd.nsq_act {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) {F : T → Matrix ι ι ℂ} (hF : Bdd F) :
    ∃ C : ℝ, ∀ t, nsq (act d v (F t)) ≤ C := by
  refine hF.cont (f := fun y => nsq (act d v y)) ?_
  simp only [nsq, act, tpow, vecMul, dotProduct, of_apply]
  fun_prop

theorem sq_le_nsq {κ : Type} [Fintype κ] (v : κ → ℂ) (k : κ) : ‖v k‖ ^ 2 ≤ nsq v :=
  Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem core {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ)
    (h1 : ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C →
      ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C')
    (h2 : ∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v)
    (c : ℝ) (hc : 0 < c) (K N D : T → Matrix ι ι ℂ) (e : T → ι → ℂ)
    (hK : ∀ t, (K t)ᴴ * K t = 1) (hKd : ∀ t, (K t).det = 1) (hNd : ∀ t, (N t).det = 1)
    (hDd : ∀ t, (D t).det = 1) (hDh : ∀ t, (D t)ᴴ = D t) (hDe : ∀ t, D t * diagonal (e t) = 1)
    (hN : Bdd N) (hN1 : Bdd fun t => D t * N t * diagonal (e t))
    (hN2 : Bdd fun t => D t * (D t * N t * diagonal (e t)) * diagonal (e t))
    (hw : ∀ t j, act d v (K t * D t * N t) j = 0 ∨ c ≤ ‖act d v (K t * D t * N t) j‖) :
    ∃ C' : ℝ, ∀ t, nsq (act d v (K t * D t * N t)) ≤ C' := by
  have amul : ∀ (u : TIdx ι d → ℂ) (y z : Matrix ι ι ℂ), act d u (y * z) = act d (act d u y) z :=
    fun u => ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.1
  have adiag : ∀ (u : TIdx ι d → ℂ) (a : ι → ℂ) (k : TIdx ι d),
      act d u (diagonal a) k = u k * ∏ j, a (k.2 j) := fun u => ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1
  have aone : act d v 1 = v := ((GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v).1
  have heD : ∀ t, diagonal (e t) * D t = 1 := fun t => mul_eq_one_comm.1 (hDe t)
  have hKK : ∀ t, K t * (K t)ᴴ = 1 := fun t => mul_eq_one_comm.1 (hK t)
  have hed : ∀ t, (diagonal (e t)).det = 1 := fun t => by
    have := congrArg Matrix.det (hDe t)
    rwa [det_mul, hDd, one_mul, det_one] at this
  obtain ⟨C₁, hC₁⟩ := ((bdd_unitary hK).mul hN1).nsq_act d v
  have hz : ∀ t, nsq (act d v (K t * D t * N t * diagonal (e t) * diagonal (e t))) ≤
      ∑ _j : TIdx ι d, (C₁ / c) ^ 2 := by
    intro t
    refine Finset.sum_le_sum fun j _ => ?_
    have h3 := (sq_le_nsq _ j).trans (hC₁ t)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, amul, adiag] at h3
    rw [amul, adiag, amul, adiag]
    rcases hw t j with h0 | h0
    · rw [h0]; simp; positivity
    · rw [norm_mul] at h3
      rw [norm_mul, norm_mul]
      set W := ‖act d v (K t * D t * N t) j‖
      set X := ‖∏ l, e t (j.2 l)‖
      have hX : 0 ≤ X := norm_nonneg _
      have hW : 0 ≤ W := norm_nonneg _
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [le_div_iff₀ hc]
      calc W * X * X * c ≤ W * X * X * W := by gcongr
        _ = (W * X) ^ 2 := by ring
        _ ≤ C₁ := h3
  obtain ⟨C₂, hC₂⟩ := h1 (∑ _j : TIdx ι d, (C₁ / c) ^ 2)
  have hex := fun t => hC₂ _ (by simp only [det_mul, hKd, hDd, hNd, hed, mul_one]) (hz t)
  choose h hd hv hb using hex
  have hb' : Bdd fun t => h t * (K t * D t * N t * diagonal (e t) * diagonal (e t)) := ⟨C₂, hb⟩
  have hω := hb'.mul hN2.adj
  have eω : ∀ t, h t * (K t * D t * N t * diagonal (e t) * diagonal (e t)) *
      (D t * (D t * N t * diagonal (e t)) * diagonal (e t)).adjugate = h t * K t * diagonal (e t) := by
    intro t
    have e1 : K t * D t * N t * diagonal (e t) * diagonal (e t) =
        K t * diagonal (e t) * (D t * (D t * N t * diagonal (e t)) * diagonal (e t)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal (e t)) (D t), heD, Matrix.one_mul]
    rw [e1, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (adjugate _), mul_adjugate]
    simp only [det_mul, hDd, hNd, hed, mul_one, one_smul, Matrix.mul_assoc]
  simp only [eω] at hω
  have hh : ∀ t, h t * (h t).adjugate = 1 := fun t => by rw [mul_adjugate, hd, one_smul]
  have eadj : ∀ t, (h t * K t * diagonal (e t)).adjugate = D t * (K t)ᴴ * (h t).adjugate := by
    intro t
    have l : (h t * K t * diagonal (e t)).adjugate * (h t * K t * diagonal (e t)) = 1 := by
      rw [adjugate_mul]; simp only [det_mul, hd, hKd, hed, mul_one, one_smul]
    have r : (h t * K t * diagonal (e t)) * (D t * (K t)ᴴ * (h t).adjugate) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (diagonal (e t)) (D t), heD, Matrix.one_mul, ← Matrix.mul_assoc (K t), hKK,
        Matrix.one_mul, hh]
    exact left_inv_eq_right_inv l r
  obtain ⟨C₃, hC₃⟩ := (hω.adj.ct.mul hN).nsq_act d v
  refine ⟨C₃, fun t => ?_⟩
  have hfix : act d v ((h t).adjugate)ᴴ = v := by
    refine h2 _ (by rw [det_adjugate, hd, one_pow]) ?_
    conv_lhs => rw [← hv t]
    rw [← amul, hh, aone]
  have := hC₃ t
  rw [eadj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDh, Matrix.mul_assoc,
    amul, hfix] at this
  exact this

theorem borel_harishChandra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), (∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C') → (∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v) → ∀ C c : ℝ, 0 < c → ∃ C' : ℝ, ∀ (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ), IsSiegel C k a n → (∀ j, act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j = 0 ∨ c ≤ ‖act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j‖) → nsq (act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ)))) ≤ C' := by
  intro ι _ _ _ m d v h1 h2 C c hc
  let φ : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hφ : ∀ y : Matrix ι ι ℝ, y.map (fun r : ℝ => (r : ℂ)) = φ y := fun _ => rfl
  have hφa : ∀ (y : Matrix ι ι ℝ) i j, φ y i j = (y i j : ℂ) := fun _ _ _ => rfl
  have hφd : ∀ y : Matrix ι ι ℝ, y.det = 1 → (φ y).det = 1 := fun y hy => by
    rw [← RingHom.map_det, hy, map_one]
  have hφh : ∀ y : Matrix ι ι ℝ, (φ y)ᴴ = φ yᵀ := fun y => by
    ext i j; simp [hφa]
  have hφdiag : ∀ a : ι → ℝ, φ (diagonal a) = diagonal fun i => (a i : ℂ) := fun a => by
    ext i j; by_cases hij : i = j <;> simp [hφa, diagonal_apply, hij]
  simp only [hφ, map_mul]
  let S := {p : Matrix ι ι ℝ × (ι → ℝ) × Matrix ι ι ℝ // IsSiegel C p.1 p.2.1 p.2.2 ∧
    ∀ j, act d v (φ p.1 * φ (diagonal p.2.1) * φ p.2.2) j = 0 ∨
      c ≤ ‖act d v (φ p.1 * φ (diagonal p.2.1) * φ p.2.2) j‖}
  have ratio : ∀ t : S, ∀ i j, t.1.2.2 i j = 0 ∨ t.1.2.1 i * (t.1.2.1 j)⁻¹ ≤ max 1 C := by
    intro t i j
    have hs := t.2.1
    rcases lt_trichotomy i j with h | h | h
    · right
      rw [← div_eq_mul_inv, div_le_iff₀ (hs.pos j)]
      exact (hs.le i j h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hs.pos j).le)
    · right; subst h; rw [mul_inv_cancel₀ (hs.pos i).ne']; exact le_max_left _ _
    · left; exact hs.lower i j h
  have nrm : ∀ t : S, ∀ i, ‖(t.1.2.1 i : ℂ)‖ = t.1.2.1 i := fun t i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (t.2.1.pos i).le]
  obtain ⟨C', hC'⟩ := core (T := S) d v h1 h2 c hc (fun t => φ t.1.1) (fun t => φ t.1.2.2)
    (fun t => φ (diagonal t.1.2.1)) (fun t i => ((t.1.2.1 i : ℂ))⁻¹)
    (fun t => by rw [hφh, ← map_mul, t.2.1.orth, map_one])
    (fun t => hφd _ t.2.1.det_k)
    (fun t => hφd _ (by
      rw [det_of_upperTriangular (fun i j h => t.2.1.lower i j h)]
      simp [t.2.1.diag]))
    (fun t => hφd _ (by rw [det_diagonal, t.2.1.prod_eq]))
    (fun t => by rw [hφh, diagonal_transpose])
    (fun t => by
      rw [hφdiag, diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      exact mul_inv_cancel₀ (by exact_mod_cast (t.2.1.pos i).ne'))
    ⟨C, fun t i j => by beta_reduce; rw [hφa, Complex.norm_real]; exact t.2.1.bdd i j⟩
    ⟨max 1 C * max 1 C, fun t i j => by
      simp only [hφdiag, mul_diagonal, diagonal_mul, hφa, norm_mul, norm_inv, nrm]
      rcases ratio t i j with h | h
      · rw [h]; simp
      · have hp := (t.2.1.pos i).le
        have hq := (t.2.1.pos j).le
        have hn : ‖(t.1.2.2 i j : ℂ)‖ ≤ max 1 C := by
          rw [Complex.norm_real]; exact (t.2.1.bdd i j).trans (le_max_right _ _)
        calc _ = (t.1.2.1 i * (t.1.2.1 j)⁻¹) * ‖(t.1.2.2 i j : ℂ)‖ := by ring
          _ ≤ _ := by gcongr⟩
    ⟨max 1 C * max 1 C * max 1 C, fun t i j => by
      simp only [hφdiag, mul_diagonal, diagonal_mul, hφa, norm_mul, norm_inv, nrm]
      rcases ratio t i j with h | h
      · rw [h]; simp
      · have hp := (t.2.1.pos i).le
        have hq := (t.2.1.pos j).le
        have hn : ‖(t.1.2.2 i j : ℂ)‖ ≤ max 1 C := by
          rw [Complex.norm_real]; exact (t.2.1.bdd i j).trans (le_max_right _ _)
        calc _ = (t.1.2.1 i * (t.1.2.1 j)⁻¹) * (t.1.2.1 i * (t.1.2.1 j)⁻¹) * ‖(t.1.2.2 i j : ℂ)‖ := by ring
          _ ≤ _ := by gcongr⟩
    (fun t => t.2.2)
  exact ⟨C', fun k a n hs hw => hC' ⟨(k, a, n), hs, hw⟩⟩

end GlobalTheory.ClassFin.SiegelBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardQuotSpanAlgebraMap
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem card_quot_span_algebraMap : ∀ (R O : Type) [CommRing R] [Nontrivial R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O] (t : R), Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (R ⧸ Ideal.span {t}) ^ Module.finrank R O := by
  intro R O _ _ _ _ _ _ t
  classical
  let b := Module.Free.chooseBasis R O
  let f : O →+ (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) :=
    { toFun := fun x i => Ideal.Quotient.mk _ (b.repr x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hsurj : Function.Surjective f := by
    intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm z, ?_⟩
    ext i
    show Ideal.Quotient.mk _ (b.equivFun (b.equivFun.symm z) i) = y i
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker : f.ker = (Ideal.span {algebraMap R O t}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · intro h
      have h' : ∀ i, ∃ a, a * t = b.repr x i := fun i => by
        have := congrFun h i
        exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
      choose a ha using h'
      refine ⟨b.equivFun.symm a, ?_⟩
      rw [mul_comm, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [← ha i, mul_comm]
    · rintro ⟨a, rfl⟩
      ext i
      show Ideal.Quotient.mk _ (b.repr _ i) = 0
      rw [mul_comm, ← Algebra.smul_def, map_smul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b.repr a i, by simp [mul_comm]⟩
  have e := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  rw [hker] at e
  have h1 : Nat.card (O ⧸ Ideal.span {algebraMap R O t}) =
      Nat.card (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) := e
  rw [h1, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R O)]

end GlobalTheory.CNorm
end

