module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0005
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.Bundle0002
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PEvEx
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

theorem pEvEx : EvEx := by
  intro p E _ _ _ T w hw
  have hk : RingHom.ker T.Φ ≤ RingHom.ker (pLoc E w) := by
    intro x hx
    exact RingHom.mem_ker.2 (((T.Φ_ker x).1 (RingHom.mem_ker.1 hx)) w hw)
  refine ⟨RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, hk⟩, fun x => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨pLoc E w, hk⟩ x

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntCof
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem UpperTheory.Gal.W2.Seed.pIntCof :
    IntCof := by
  intro E _ _ n a
  have key : ∀ x : Af E, ∀ᶠ w : Plc E in Filter.cofinite, pLoc E w x ∈ w.adicCompletionIntegers E :=
    fun x => x.2
  have h1 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key (a.val i j)))
  have h2 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key ((a⁻¹).val i j)))
  filter_upwards [h1, h2] with w ha hb
  refine mem_GLint_of_entries (w.adicCompletionIntegers E).toSubring _ (fun i j => ha i j) (fun i j => ?_)
  rw [← map_inv]
  exact hb i j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
section
noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def dv (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : ℂ :=
  if 0 < (σ (A.hd n i : E)).re then Complex.I else -Complex.I

private theorem hd_ne (hS : HdSign) (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : (σ (A.hd n i : E)).re ≠ 0 := by
  obtain ⟨-, -, h1, h2⟩ := hS E A n σ i
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0
  · exact (h1 h).ne'
  · exact (h2 h).ne

private theorem dv_sq (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : dv A n σ i * dv A n σ i = -1 := by
  unfold dv; split_ifs <;> simp

private theorem dv_conj (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) :
    (starRingEnd ℂ) (dv A n σ i) = -dv A n σ i := by
  unfold dv; split_ifs <;> simp

private theorem gram_diag (A : Arith E) (n : ℕ) (σ : E →+* ℂ) :
    gramAt (A.H n) σ = Matrix.diagonal fun i => σ (A.hd n i : E) := by
  ext i j
  simp only [gramAt, Arith.H, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem real_abs (h : ℂ) (hi : h.im = 0) (hr : h.re ≠ 0) :
    -Complex.I * (h * (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) ∧
    Complex.I * (h * (starRingEnd ℂ) (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) := by
  have hh : h = ((h.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
  split_ifs with hp
  · rw [abs_of_pos hp]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hr)]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp

open scoped ComplexOrder in
private theorem posDiag {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal fun i => ((a i : ℝ) : ℂ)).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact Complex.zero_lt_real.mpr (ha i)

open scoped Classical ComplexOrder in
private theorem orient_core (hT : TraceType) (hS : HdSign) (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) (hrep : RepOK A n rep) :
    ∃ J : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E, J * J = -1 ∧
      (starT (hermStar (A.H n) (A.det_ne n)) ℝ J).unop = -J ∧
      (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
      ∀ v : InfinitePlace E, ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        (gramAt (A.H n) v.embedding * evM v.embedding J)).PosDef := by
  obtain ⟨J, hJ⟩ := (cmField_real_tensor_matrix_bijective_cmType hT A n).2 (fun τ : Phi A => Matrix.diagonal (dv A n τ.1))
  have hJτ : ∀ τ : Phi A, evM τ.1 J = Matrix.diagonal (dv A n τ.1) := fun τ => congrFun hJ τ
  have hne : ∀ (σ : E →+* ℂ) (i : Fin n), σ (A.hd n i : E) ≠ 0 := fun σ i h0 =>
    hd_ne hS A n σ i (by rw [h0]; simp)
  obtain ⟨β, hβ1, hβ2⟩ := hrep
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    rw [map_mul, map_neg, map_one, hJτ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dv_sq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    have key := evM_star (A.H n) (A.herm n) (A.det_ne n) τ.1 J
    rw [gram_diag, hJτ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at key
    rw [map_neg, hJτ]
    ext i j
    have hk := congrFun (congrFun key i) j
    rw [Matrix.diagonal_mul] at hk
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.neg_apply] at hk ⊢
      apply mul_left_cancel₀ (hne τ.1 i)
      rw [hk, Complex.star_def, dv_conj]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, neg_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left (hne τ.1 i)
  · intro x hx
    rw [cmField_hermitianForm_baseChange_real_eq_sum hT A n (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) hβ1]
    have hterm : ∀ k : Phi A × Fin n,
        Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) (actOn rep ℝ J x) k =
          dv A n k.1.1 k.2 * Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k := by
      rintro ⟨τ, i⟩
      rw [Th_act (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) rep hβ2 J x τ i,
        hJτ, Matrix.mulVec_diagonal]
    have hz : ∃ k, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      apply cmType_trace_embedding_injective_of_linearEquiv hT A n β
      rw [map_zero]
      funext k
      exact hc k
    obtain ⟨k₀, hk₀⟩ := hz
    have tp := fun (τ : Phi A) (i : Fin n) (z : ℂ) => term_pos (τ.1 A.δ) (τ.1 (A.hd n i : E)) z
      (hS E A n τ.1 i).2.1 (A.δ_sign τ.1 τ.2) (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)
    apply Finset.sum_pos'
    · rintro ⟨τ, i⟩ -
      rw [hterm]
      unfold dv
      exact mul_nonneg two_pos.le (tp τ i _).1
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      obtain ⟨τ, i⟩ := k₀
      rw [hterm]
      unfold dv
      exact mul_pos two_pos ((tp τ i _).2 hk₀)
  · intro v
    obtain ⟨τ, hτv, -⟩ := (hT E A).2.2.1 v
    subst hτv
    have hω := (hT E A).2.2.2
    rcases InfinitePlace.embedding_mk_eq (τ : E →+* ℂ) with he | he
    · rw [he, if_pos τ.2, gram_diag, hJτ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (-Complex.I • fun i => τ.1 (A.hd n i : E) * dv A n τ.1 i) =
          fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).1
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)
    · have hc : ¬ (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.ω : E) = A.τ₀ (A.ω : E) := by
        intro h
        rw [ComplexEmbedding.conjugate_coe_eq, τ.2] at h
        exact hω (Complex.conj_eq_iff_im.mp h)
      rw [he, if_neg hc, gram_diag, evM_conj, hJτ, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (Complex.I • fun i => (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.hd n i : E) *
          (starRingEnd ℂ) (dv A n τ.1 i)) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq]
        rw [Complex.conj_eq_iff_im.mpr (hS E A n τ.1 i).1]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).2
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)

end UpperTheory.Gal.W2.Seed.Ori

theorem UpperTheory.Gal.W2.Seed.pOrient :
    TraceType → HdSign → Orient := by
  intro hT hS E _ _ _ A n hn hs p _ P rep hrep
  exact UpperTheory.Gal.W2.Seed.Ori.orient_core hT hS A n rep hrep
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPIntRev
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed.IntRev

private theorem mem_range_map {R : Type} [CommRing R] (S : Subring R) {m : ℕ} (x : GL (Fin m) R)
    (h1 : ∀ i j, x.1 i j ∈ S) (h2 : ∀ i j, (x⁻¹).1 i j ∈ S) : x ∈ (GeneralLinearGroup.map S.subtype).range := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]

private theorem norm_le (τ : E →+* PadicAlgCl p) (x : E)
    (h : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) : ‖τ x‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, -, hNc, hN⟩ := GlobalTheory.HilbertThetaSeries.DenP.exists_away hp x
  have hint : IsIntegral ℤ ((N : E) * x) := by
    refine (GlobalTheory.HilbertThetaSeries.DenP.isIntegral_iff_val _).2 fun w => ?_
    by_cases hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, GlobalTheory.HilbertThetaSeries.DenP.val_coprime hNc hw, one_mul]; exact h w hw
    · exact hN w hw
  have h1 : ‖τ ((N : E) * x)‖ ≤ 1 := GlobalTheory.CongW.PlaceEmb.norm_int_le τ ⟨_, hint⟩
  have h3 : ‖(N : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).2 hNc.symm
  have h2 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← h3, ← PadicAlgCl.norm_extends p, map_natCast]
  rwa [map_mul, map_natCast, norm_mul, h2, one_mul] at h1

variable [IsCMField E] {n : ℕ}

private theorem entry_le (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n))
    (τ : E →+* PadicAlgCl p) (i j : Fin n) : ‖τ (y.1.1.val i j)‖ ≤ 1 := by
  refine norm_le τ _ fun w hw => ?_
  have h1 : (comp w (rat y)).val i j ∈ w.adicCompletionIntegers E := (GlobalTheory.AdelicU.mem_GLint_iff.1 (hy w hw)).1 i j
  have h2 : (comp w (rat y)).val i j = ((y.1.1.val i j : E) : w.adicCompletion E) := rfl
  rw [h2, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

private theorem hyp_inv (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n)) :
    ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y⁻¹) ∈ GlobalTheory.LFun.KGL w (n := n) := fun w hw => by
  rw [map_inv, map_inv]; exact inv_mem (hy w hw)

private theorem mult_le (hn : 0 < n) (τ : E →+* PadicAlgCl p) (y : Gam0 E n)
    (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w (n := n)) :
    algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have h : (y.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * y.1.1.val =
      algebraMap ℚ E y.1.2 • (1 : Matrix (Fin n) (Fin n) E) := y.2.1
  have h0 := congrArg τ (congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  have e : algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) = τ (algebraMap ℚ E y.1.2) := by
    simp only [eq_ratCast, map_ratCast]
  rw [e, ← h0]
  refine sum_mem fun k _ => ?_
  rw [map_mul]
  exact mul_mem (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy (τ.comp (GlobalTheory.SplitPts.conjE E).toRingHom) k ⟨0, hn⟩))
    (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy τ k ⟨0, hn⟩))

omit [NumberField E] [IsCMField E] in
private theorem incl_mem (τ : E →+* PadicAlgCl p) (x : E) (hx : ‖τ x‖ ≤ 1) :
    GlobalTheory.LKRes.inclK p (FwOf τ) 1 (embOf τ x) ∈ GlobalTheory.LKRes.intKQ p (FwOf τ) 1 :=
  Subring.subset_closure (Or.inl ⟨⟨embOf τ x, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 hx⟩, rfl⟩)

end UpperTheory.Gal.W2.Seed.IntRev

open UpperTheory.Gal.W2.Seed.IntRev in
theorem UpperTheory.Gal.W2.Seed.pPIntRev :
    IntConj → PIntRev := by
  intro _ E _ _ _ A n p _ S y hy
  have hn : 0 < n := S.facts.pos
  have hy' := hyp_inv y hy
  refine Subgroup.mem_prod.2 ⟨mem_range_map _ _ (fun i j => ?_) (fun i j => ?_),
    (Subgroup.mem_pi _).2 fun k _ => mem_range_map _ _ (fun i j => ?_) (fun i j => ?_)⟩
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y hy
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y⁻¹ hy'
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · exact incl_mem (S.P.emb k) (y.1.1.val i j) (entry_le y hy (S.P.emb k) i j)
  · exact incl_mem (S.P.emb k) ((y⁻¹).1.1.val i j) (entry_le y⁻¹ hy' (S.P.emb k) i j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PVecCoord
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma one_tmul_smul_eq_add_of_algebraMap_eq_add {M R : Type} [AddCommGroup M] [CommRing R] [Algebra ℚ R] (r : R) (q : ℚ) (y : M) :
    (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M)) = (q • r) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M) := by
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp

theorem UpperTheory.Gal.W2.Seed.pVecCoord :
    LatCoord → EvEx → VecCoord := by
  intro hLat hEv E _ _ _ A n p _ S T
  obtain ⟨ν, hν1, hν2, hν3⟩ := hLat E A n p S T.μ T.mu
  choose ev hev using fun (w : Plc E) (hw : (p : 𝓞 E) ∉ w.asIdeal) => hEv p E T.toAdT w hw
  let co : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → (AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E)) := fun w hw =>
    { toFun := fun v i => ev w hw (ν v i)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  let vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E) := fun w =>
    if hw : (p : 𝓞 E) ∉ w.asIdeal then co w hw else 0
  have hvec : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) v i, vec w v i = ev w hw (ν v i) := fun w hw v i => by
    simp only [vec, dif_pos hw]; rfl
  have hE : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) (c : 𝓞 E), ev w hw ((1 : AfP p) ⊗ₜ[ℚ] (c : E)) = algebraMap (𝓞 E) (w.adicCompletion E) c := by
    intro w hw c
    rw [← T.Φ_E, hev]
    rfl
  have hν4 : ∀ (r : AfP p) (q : ℚ) (y : Fin n → 𝓞 E) i, ν (r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] (y : S.D.La) : VQ S.D))) i = (q • r) ⊗ₜ[ℚ] (y i : E) := by
    intro r q y i
    exact (congrArg (fun z => ν z i) (one_tmul_smul_eq_add_of_algebraMap_eq_add (M := S.D.La) r q y)).trans (hν1 _ y i)
  refine ⟨vec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    apply ν.injective
    rw [map_zero]
    funext i
    obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
    rw [Pi.zero_apply, ← hx, T.Φ_ker]
    intro w hw
    have := congrFun (h w hw) i
    rw [hvec w hw, ← hx, hev] at this
    exact this
  · intro v
    rw [hν3]
    constructor
    · intro h w hw i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      have := (T.Φ_int x).1 (hx ▸ h i) w hw
      rw [hvec w hw, ← hx, hev]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this
    · intro h i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      rw [← hx, T.Φ_int]
      intro w hw
      have := h w hw i
      rw [hvec w hw, ← hx, hev] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  · intro y hy
    let x : Fin n → Af E := fun i => ⟨fun w => y w i, Filter.Eventually.of_forall fun w => hy w i⟩
    refine ⟨ν.symm (fun i => T.Φ (x i)), fun w hw => ?_⟩
    funext i
    rw [hvec w hw, ν.apply_symm_apply, hev]
    rfl
  · intro w hw y i
    rw [hvec w hw, ← hE w hw]
    congr 1
    exact hν1 1 y i
  · intro w hw g v
    funext i
    rw [hvec w hw, hν2, T.j_mx, RingHom.map_mulVec]
    have hG : GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹ =
        GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
      simp [UpperTheory.Gal.CertificateRingHomMap.comp]
    have hM : (((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val).map T.Φ).map (ev w hw) =
        (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val := by
      exact Matrix.ext fun a b => hev w hw _
    have hV : (ev w hw) ∘ (ν v) = vec w v := funext fun k => (hvec w hw v k).symm
    rw [hM, hV, hG]
  · intro w hw c v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), smul_add]
    | tmul r u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), smul_add]
      | tmul q y =>
        let y' : Fin n → 𝓞 E := y
        have key : UpperTheory.Gal.Int.Geo.mulF S.D c (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) =
            r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] ((c • y' : Fin n → 𝓞 E) : S.D.La) : VQ S.D)) := by
          simp only [UpperTheory.Gal.Int.Geo.mulF, LinearMap.baseChange_tmul, actQ]
          rfl
        funext i
        have e2 : ν (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) i = (q • r) ⊗ₜ[ℚ] (y' i : E) := hν4 r q y' i
        have e3 : (((c • y') i : 𝓞 E) : E) = (c : E) * (y' i : E) := by simp [Pi.smul_apply]
        rw [key, Pi.smul_apply, hvec w hw, hvec w hw, hν4, e2, e3, ← hE w hw, smul_eq_mul, ← map_mul (ev w hw),
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

