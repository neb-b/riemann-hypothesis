module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIndefiniteUnitaryBoostHilbertSchmidt
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Boost

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem boost_exists : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := by
  intro m ε a b ha hb hn
  set c2 : ℝ := ∑ j, ‖a j‖ ^ 2 with hc2
  set nb : ℝ := ∑ j, ‖b j‖ ^ 2 with hnb
  have hnb0 : 0 ≤ nb := Finset.sum_nonneg fun _ _ => by positivity
  have hc1 : 1 ≤ c2 := by linarith
  have hJa : Jm ε *ᵥ a = a := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [ha i, h]
  have hJb : Jm ε *ᵥ b = -b := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [hb i, h]
  have hJa' : ∀ w, star a ⬝ᵥ (Jm ε *ᵥ w) = star a ⬝ᵥ w := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, h]
  have hJb' : ∀ w, star b ⬝ᵥ (Jm ε *ᵥ w) = -(star b ⬝ᵥ w) := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [hb i, h]
  have haa : star a ⬝ᵥ a = (c2 : ℂ) := by
    simp only [dotProduct, hc2, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast; rfl
  have hbb : star b ⬝ᵥ b = (c2 : ℂ) - 1 := by
    have : star b ⬝ᵥ b = (nb : ℂ) := by
      simp only [dotProduct, hnb, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
      push_cast; rfl
    rw [this, hn]; push_cast; ring
  have hab : star a ⬝ᵥ b = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  have hba : star b ⬝ᵥ a = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]

  set s : ℝ := Real.sqrt c2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hc1
  have hss : s ^ 2 = c2 := Real.sq_sqrt (by linarith)
  set S : ℂ := (s : ℂ) with hS
  have hS0 : S ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s ≠ 0)
  have hS1 : S + 1 ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s + 1 ≠ 0)
  have hSS : S ^ 2 = (c2 : ℂ) := by rw [hS]; exact_mod_cast hss
  set α : ℂ := (S - 1) / S ^ 2 with hα
  set β : ℂ := 1 / (S + 1) with hβ
  set γ : ℂ := 1 / S with hγ
  have hsα : star α = α := by simp [hα, hS, Complex.conj_ofReal]
  have hsβ : star β = β := by simp [hβ, hS, Complex.conj_ofReal]
  have hsγ : star γ = γ := by simp [hγ, hS, Complex.conj_ofReal]
  set A : Matrix (Fin m) (Fin m) ℂ := 1 + α • vecMulVec a (star a) + β • vecMulVec b (star b) + γ • (vecMulVec b (star a) + vecMulVec a (star b)) with hA
  have hmul : ∀ w, A *ᵥ w = w + (α * (star a ⬝ᵥ w) + γ * (star b ⬝ᵥ w)) • a + (β * (star b ⬝ᵥ w) + γ * (star a ⬝ᵥ w)) • b := by
    intro w
    simp only [hA, add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec]
    module
  have hherm : Aᴴ = A := by
    simp only [hA, conjTranspose_add, conjTranspose_smul, conjTranspose_one, conjTranspose_vecMulVec, star_star, hsα, hsβ, hsγ]
    rw [add_comm (vecMulVec a (star b))]
  have hU : A ∈ UJset ε := by
    show Aᴴ * Jm ε * A = Jm ε
    rw [hherm, Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec, hmul, hmul]
    simp only [mulVec_add, mulVec_smul, hJa, hJb, dotProduct_add, dotProduct_smul, dotProduct_neg, hJa', hJb', haa, hbb, hab, hba, smul_eq_mul]
    set p := star a ⬝ᵥ v
    set q := star b ⬝ᵥ v
    have hX : α * p + γ * q + α * (p + (α * p + γ * q) * (c2 : ℂ)) + γ * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    have hY : -(β * q + γ * p) + β * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) + γ * (p + (α * p + γ * q) * (c2 : ℂ)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    linear_combination (norm := module) hX • a + hY • b

  have hAa : A *ᵥ a = S • (a + b) := by
    rw [hmul, haa, hba]
    have e1 : α * (c2 : ℂ) + 1 = S := by rw [hα, ← hSS]; field_simp; try ring
    have e2 : γ * (c2 : ℂ) = S := by rw [hγ, ← hSS]; field_simp; try ring
    linear_combination (norm := module) e1 • a + e2 • b
  have hsq : A * A = 1 + (2 * α + α ^ 2 * (c2 : ℂ) + γ ^ 2 * ((c2 : ℂ) - 1)) • vecMulVec a (star a)
      + (2 * β + β ^ 2 * ((c2 : ℂ) - 1) + γ ^ 2 * (c2 : ℂ)) • vecMulVec b (star b)
      + (2 * γ + α * γ * (c2 : ℂ) + γ * β * ((c2 : ℂ) - 1)) • (vecMulVec a (star b) + vecMulVec b (star a)) := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, hmul, hmul]
    simp only [add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec, dotProduct_add, dotProduct_smul, haa, hbb, hab, hba, smul_eq_mul]
    module
  have htr : trace (A * A) = (m : ℂ) + 4 * (c2 : ℂ) - 4 := by
    have e1 : a ⬝ᵥ star a = (c2 : ℂ) := by rw [dotProduct_comm]; exact haa
    have e2 : b ⬝ᵥ star b = (c2 : ℂ) - 1 := by rw [dotProduct_comm]; exact hbb
    have e3 : a ⬝ᵥ star b = 0 := by rw [dotProduct_comm]; exact hba
    have e4 : b ⬝ᵥ star a = 0 := by rw [dotProduct_comm]; exact hab
    rw [hsq]
    simp only [trace_add, trace_smul, trace_one, trace_vecMulVec, Fintype.card_fin, smul_eq_mul, e1, e2, e3, e4]
    rw [hα, hβ, hγ, ← hSS]; field_simp; try ring
  have hT : ∑ i, ∑ j, ‖A i j‖ ^ 2 = (m : ℝ) + 4 * c2 - 4 := by
    have : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = trace (A * A) := by
      push_cast
      simp only [trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.mul_conj']
      congr 1
      have := congrFun (congrFun hherm j) i
      rw [conjTranspose_apply] at this
      show _ = A j i
      exact this
    rw [htr] at this
    exact_mod_cast this
  have hab2 : ∑ i, ‖a i + b i‖ ^ 2 = c2 + nb := by
    rw [hc2, hnb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  refine ⟨A, hU, fun i => ?_, ?_⟩
  · have := congrFun hAa i
    rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    exact this
  · have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    unfold hsn
    rw [Real.sq_sqrt h0, hT, hab2]
    linarith

end GlobalTheory.Boost
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFockProjectionMaximalMinors
section
open Classical MeasureTheory

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RatProj

section Form

variable {σ : Type}

def fockQ (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ)

theorem fockQ_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp

def fockQL : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ fockQ
    (by
      intro f f' g
      rw [fockQ_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockQ_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockQ_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_add]; ring)
    (by
      intro c f g
      rw [fockQ_eq_sum (c • f) g f.support support_smul, fockQ, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockQ, MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockQ, coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

theorem fockQL_apply (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl

theorem fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by
  rw [Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem eq_zero_of_fockQ_self {f : MvPolynomial σ ℚ} (h : fockQ f f = 0) : f = 0 := by
  by_contra hf
  have hf' : map (algebraMap ℚ ℂ) f ≠ 0 := by
    intro h0
    apply hf
    exact map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  have := GlobalTheory.MinorFrame.fockS_self_re_pos hf'
  rw [fockS_map, h] at this
  simp at this

end Form

variable {ι : Type} [Fintype ι]

def prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : MvPolynomial (Var ι d a) ℚ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a => (X (τ, (T τ j).1 i, i') : MvPolynomial (Var ι d a) ℚ)).det

theorem map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by
  simp only [prodMinorsQ, prodMinors, minorAt, map_prod]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]

end GlobalTheory.MinorFrame.RatProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquiv
section
namespace GlobalTheory.SepReal

private def optSumLeft (α β : Type) : Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

theorem exists_signs_equiv {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card) :
    ∃ e : Option (Fin n) ≃ Fin (n + 1), Signs e ε ε' := by
  classical
  have hF : Fintype.card {a // ¬ ε a = true} = Fintype.card {i // ¬ ε' i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Bool.not_eq_true] using h
  have hT : Fintype.card {a // ε a = true} = Fintype.card (Option {i // ε' i = true}) := by
    have h1 := Fintype.card_subtype_compl (fun a => ε a = true)
    have h2 := Fintype.card_subtype_compl (fun i => ε' i = true)
    have h3 := Fintype.card_subtype_le (fun a => ε a = true)
    have h4 := Fintype.card_subtype_le (fun i => ε' i = true)
    simp only [Fintype.card_fin] at h1 h2 h3 h4
    rw [Fintype.card_option]
    omega
  let eT := Fintype.equivOfCardEq hT
  let eF := Fintype.equivOfCardEq hF
  let e : Option (Fin n) ≃ Fin (n + 1) :=
    ((Equiv.optionCongr (Equiv.sumCompl fun i => ε' i = true).symm).trans
      (optSumLeft _ _)).trans ((Equiv.sumCongr eT.symm eF.symm).trans (Equiv.sumCompl fun a => ε a = true))
  refine ⟨e, ?_, ?_⟩
  · show ε ((eT.symm none : {a // ε a = true}) : Fin (n + 1)) = true
    exact (eT.symm none).2
  · intro i
    by_cases hi : ε' i = true
    · have : e (some i) = ((eT.symm (some ⟨i, hi⟩) : {a // ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this, (eT.symm (some ⟨i, hi⟩)).2, hi]
    · have : e (some i) = ((eF.symm ⟨i, hi⟩ : {a // ¬ ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this]
      have := (eF.symm ⟨i, hi⟩).2
      simp only [Bool.not_eq_true] at this hi
      rw [this, hi]

end GlobalTheory.SepReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
section
open Matrix Module

namespace GlobalTheory.RectSVD

theorem exists_orthonormalBasis_singularValues {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {p q : ℕ} (hp : finrank ℂ F = p) (hq : finrank ℂ E = q) (T : E →ₗ[ℂ] F) :
    ∃ (u : OrthonormalBasis (Fin p) ℂ F) (v : OrthonormalBasis (Fin q) ℂ E), ∀ i j,
      inner ℂ (u i) (T (v j)) =
        if (i : ℕ) = (j : ℕ) then ((T.singularValues i : ℝ) : ℂ) else 0 := by
  classical
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set σ : ℕ → ℝ := fun i => T.singularValues i with hσ
  have key : ∀ j k : Fin q, inner ℂ (T (v j)) (T (v k)) =
      if j = k then ((σ k : ℝ) : ℂ) ^ 2 else 0 := by
    intro j k
    have h1 := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hq k
    rw [← T.sq_singularValues_fin hq k] at h1
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (v j) ((LinearMap.adjoint T ∘ₗ T) (v k)) = _
    rw [hv, h1, inner_smul_right, orthonormal_iff_ite.mp (OrthonormalBasis.orthonormal _)]
    split_ifs <;> simp [hσ]
  have hlt : ∀ i : ℕ, σ i ≠ 0 → i < p ∧ i < q := by
    intro i hi
    have h1 : i ∈ T.singularValues.support := Finsupp.mem_support_iff.mpr hi
    rw [T.support_singularValues, Finset.mem_range] at h1
    refine ⟨h1.trans_le (hp ▸ Submodule.finrank_le _), h1.trans_le (hq ▸ LinearMap.finrank_range_le T)⟩
  let w : Fin p → F := fun i =>
    if h : (i : ℕ) < q then ((σ i : ℂ))⁻¹ • T (v ⟨i, h⟩) else 0
  have hw : Orthonormal ℂ (({i : Fin p | σ i ≠ 0} : Set (Fin p)).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨k, hk⟩
    have hi' : σ i ≠ 0 := hi
    have hk' : σ k ≠ 0 := hk
    have hkc : (σ k : ℂ) ≠ 0 := by exact_mod_cast hk'
    simp only [Set.domRestrict_apply, w, dif_pos (hlt _ hi').2, dif_pos (hlt _ hk').2,
      inner_smul_left, inner_smul_right, key, Subtype.mk.injEq, Fin.mk.injEq, Fin.ext_iff]
    split_ifs with h
    · rw [h]
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · simp
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by rw [hp, Fintype.card_fin])
  refine ⟨u, v, fun i j => ?_⟩
  by_cases hj : σ j = 0
  · have h0 : T (v j) = 0 := by
      have := key j j
      rw [if_pos rfl, hj] at this
      simpa using this
    rw [h0, inner_zero_right]
    split_ifs with h
    · have : T.singularValues i = 0 := by rw [h]; exact hj
      simp [this]
    · rfl
  · have hjc : (σ j : ℂ) ≠ 0 := by exact_mod_cast hj
    have h1 := hu ⟨j, (hlt _ hj).1⟩ hj
    have h2 : T (v j) = (σ j : ℂ) • u ⟨j, (hlt _ hj).1⟩ := by
      rw [h1]
      simp only [w, dif_pos j.isLt, Fin.eta, smul_smul, mul_inv_cancel₀ hjc, one_smul]
    rw [h2, inner_smul_right, orthonormal_iff_ite.mp u.orthonormal]
    simp only [Fin.ext_iff]
    split_ifs with h
    · simp [h, hσ]
    · simp

theorem exists_svd_singularValues (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
          * Vᴴ := by
  obtain ⟨u, v, h⟩ := exists_orthonormalBasis_singularValues
    (E := EuclideanSpace ℂ (Fin q)) (F := EuclideanSpace ℂ (Fin p)) (p := p) (q := q)
    (by simp) (by simp) (Matrix.toEuclideanLin B)
  have hU := (EuclideanSpace.basisFun (Fin p) ℂ).toMatrix_orthonormalBasis_mem_unitary u
  have hV := (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary v
  refine ⟨_, hU, _, hV, ?_⟩
  set U := (EuclideanSpace.basisFun (Fin p) ℂ).toBasis.toMatrix u with hUd
  set V := (EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix v with hVd
  have hD : (Matrix.of fun (i : Fin p) (j : Fin q) =>
      if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
        = Uᴴ * B * V := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.mul_assoc]
    simp [hUd, hVd, Matrix.mul_apply, Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec,
      dotProduct, mul_comm]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

theorem exists_svd : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  intro p q B
  obtain ⟨U, hU, V, hV, h⟩ := exists_svd_singularValues p q B
  exact ⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩

end GlobalTheory.RectSVD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversalStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal : ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G), Measurable e → mK Kᶜ = 0 → (∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) → lam ≠ 0 → (∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤) → (∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧ ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) → ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f → ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  first | exact @GlobalTheory.Twist.lintegral_haar_eq_transversal | exact GlobalTheory.Twist.lintegral_haar_eq_transversal | (intros; apply GlobalTheory.Twist.lintegral_haar_eq_transversal <;> assumption)
end

