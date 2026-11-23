module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.GLDelta
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

namespace GLChiPf

open Matrix

variable {k : Type} [Field k] {n : ℕ}

def glOf (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  ⟨M, M⁻¹, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h),
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)⟩

theorem chi_conj (χ : GL (Fin n) k →* ℚ) (s x : GL (Fin n) k) : χ (s * x * s⁻¹) = χ x := by
  rw [map_mul, map_mul, mul_comm (χ s), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem diag_transvection [CharZero k] (i j : Fin n) (hij : i ≠ j) (c : k) :
    diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j (2 * c) := by
  ext a b
  simp only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Function.update_apply, Pi.one_apply, eq_comm (a := i) (b := a),
    eq_comm (a := j) (b := b)]
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    by_cases hjb : b = j <;> simp_all

theorem chi_transvection [CharZero k] (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (t : TransvectionStruct (Fin n) k) (h : t.toMatrix.det ≠ 0) : χ (glOf t.toMatrix h) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have key : ∀ a : k, a ≠ 0 → diagonal (Function.update (1 : Fin n → k) i a) *
      diagonal (Function.update (1 : Fin n → k) i a⁻¹) = 1 := by
    intro a ha
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx; simp [ha]
    · simp [Function.update_apply, hx]
  have key' : diagonal (Function.update (1 : Fin n → k) i 2⁻¹) *
      diagonal (Function.update (1 : Fin n → k) i 2) = 1 := by
    simpa using key 2⁻¹ (inv_ne_zero h2)
  let s : GL (Fin n) k := ⟨diagonal (Function.update (1 : Fin n → k) i 2),
    diagonal (Function.update (1 : Fin n → k) i 2⁻¹), key 2 h2, key'⟩
  have hsq : s * glOf _ h * s⁻¹ = glOf _ h * glOf _ h := by
    apply Units.ext
    change diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j c * transvection i j c
    rw [diag_transvection i j hij c, two_mul]
    symm
    apply transvection_mul_transvection_same
    all_goals exact hij
  have e := chi_conj χ s (glOf _ h)
  rw [hsq, map_mul] at e
  exact mul_left_cancel₀ (ne_of_gt (hpos _)) (e.trans (mul_one _).symm)

def dU : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem dU_val (D : Fin n → kˣ) :
    ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (D i : k)) := rfl

theorem perm_conj (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (M : Matrix (Fin n) (Fin n) k) :
    σ.toPEquiv.toMatrix * M * σ.toPEquiv.toMatrix = M.submatrix σ σ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl

theorem perm_sq (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) :
    σ.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) k) := by
  have e := perm_conj σ hσ (1 : Matrix (Fin n) (Fin n) k)
  rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at e

def sU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, perm_sq σ hσ, perm_sq σ hσ⟩

theorem sU_conj_dU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (D : Fin n → kˣ) :
    sU σ hσ * dU D * (sU σ hσ)⁻¹ = dU (D ∘ σ) := by
  apply Units.ext
  show σ.toPEquiv.toMatrix * ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * σ.toPEquiv.toMatrix =
    ((dU (D ∘ σ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [dU_val, dU_val, perm_conj σ hσ, Matrix.submatrix_diagonal_equiv]
  rfl

theorem mulSingle_comp_swap (i j : Fin n) (d : kˣ) :
    (Pi.mulSingle i d : Fin n → kˣ) ∘ (Equiv.swap i j) = Pi.mulSingle j d := by
  funext x
  simp only [Function.comp_apply]
  by_cases hxj : x = j
  · subst hxj; simp
  · by_cases hxi : x = i
    · subst hxi
      rw [Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hxj), Pi.mulSingle_eq_of_ne hxj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, Pi.mulSingle_eq_of_ne hxi, Pi.mulSingle_eq_of_ne hxj]

theorem chi_single_eq (χ : GL (Fin n) k →* ℚ) (i j : Fin n) (d : kˣ) :
    χ (dU (Pi.mulSingle i d)) = χ (dU (Pi.mulSingle j d)) := by
  have h := chi_conj χ (sU (Equiv.swap i j) (Equiv.symm_swap i j)) (dU (Pi.mulSingle i d))
  rw [sU_conj_dU, mulSingle_comp_swap] at h
  exact h.symm

theorem chi_single (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (i : Fin n) (d : kˣ) : χ (dU (Pi.mulSingle i d)) = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact i.elim0
  have hsc : Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d = dU (fun _ => d) := by
    apply Units.ext
    rw [dU_val]
    ext a b
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
  have hprod : (fun _ : Fin n => d) = ∏ l, Pi.mulSingle l d := (Finset.univ_prod_mulSingle (fun _ => d)).symm
  have h1 : (χ.comp dU) (fun _ => d) = 1 := by rw [MonoidHom.comp_apply, ← hsc]; exact hz d
  rw [hprod, map_prod] at h1
  simp only [MonoidHom.comp_apply] at h1
  have h2 : ∏ l : Fin n, χ (dU (Pi.mulSingle l d)) = ∏ _l : Fin n, χ (dU (Pi.mulSingle i d)) :=
    Finset.prod_congr rfl (fun l _ => chi_single_eq χ l i d)
  rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact (pow_eq_one_iff_of_nonneg (hpos _).le hn).mp h1

theorem chi_diag (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (D : Fin n → kˣ) : χ (dU D) = 1 := by
  have e : χ (dU D) = (χ.comp dU) (∏ i, Pi.mulSingle i (D i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod]
  exact Finset.prod_eq_one (fun i _ => chi_single χ hpos hz i (D i))

end GLChiPf

open GLChiPf in
theorem gl_character : GLChi := by
  intro k _ _ n χ hpos hz g
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) k)
  have htd : ∀ t : Matrix.TransvectionStruct (Fin n) k, t.toMatrix.det ≠ 0 := fun t => by
    rw [t.det]; exact one_ne_zero
  have lu_val : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (((l.map fun t => glOf t.toMatrix (htd t)).prod : Matrix.GeneralLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = (l.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]
      try rfl
  have lu_chi : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      χ ((l.map fun t => glOf t.toMatrix (htd t)).prod) = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih, chi_transvection χ hpos t (htd t), one_mul]
  have det_l : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (l.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, t.det, ih, one_mul]
  have hg0 : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hdet : (g : Matrix (Fin n) (Fin n) k).det = ∏ j, D j := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, det_l, det_l, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    rw [hdet] at hg0
    exact Finset.prod_ne_zero_iff.mp hg0 i (Finset.mem_univ i)
  have hg : g = (L.map fun t => glOf t.toMatrix (htd t)).prod * dU (fun i => Units.mk0 (D i) (hD i)) *
      (L'.map fun t => glOf t.toMatrix (htd t)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, lu_val, lu_val, dU_val]
    exact hM
  rw [hg, map_mul, map_mul, lu_chi, lu_chi, chi_diag χ hpos hz, one_mul, one_mul]

end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowD
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S

theorem exists_nonfixed (I : AutInst) : ∃ θ : I.E, star θ ≠ θ := by
  by_contra h
  push Not at h
  have htop : (⊥ : Subalgebra I.F I.E) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := RingHom.mem_range.1 ((I.cm.fixed x).1 (h x))
    exact Algebra.mem_bot.2 ⟨a, ha⟩
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [I.cm.deg2] at h1
  exact absurd h1 (by norm_num)

theorem decompE (I : AutInst) (θ : I.E) (hθ : star θ ≠ θ) (e : I.E) :
    ∃ f g : I.F, e = f • (1 : I.E) + g • θ := by
  have hli : LinearIndependent I.F ![(1 : I.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hθ
      have h' : s • (1 : I.E) = -(t • θ) := eq_neg_of_add_eq_zero_left hst
      have hθeq : algebraMap I.F I.E (-(t⁻¹ * s)) = θ := by
        rw [Algebra.algebraMap_eq_smul_one, neg_smul, mul_smul, h', smul_neg, neg_neg,
          smul_smul, inv_mul_cancel₀ ht, one_smul]
      exact (I.cm.fixed θ).2 (RingHom.mem_range.2 ⟨_, hθeq⟩)
    refine ⟨?_, ht⟩
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact hst.resolve_right one_ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [I.cm.deg2])
  have he : e ∈ Submodule.span I.F (Set.range ![(1 : I.E), θ]) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.F).1 he
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp

theorem decompV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (θ : I.E) (hθ : star θ ≠ θ)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    ∃ p q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v, x = p ⊗ₜ 1 + q ⊗ₜ θ := by
  induction x using TensorProduct.inductionOn with
  | tmul a e =>
    obtain ⟨f, g, rfl⟩ := decompE I θ hθ e
    exact ⟨f • a, g • a, by rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

theorem incL_apply (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    incL I v p = p ⊗ₜ 1 := rfl

theorem sigV_incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    sigV I v (incL I v p) = incL I v p := by
  rw [incL_apply]
  simp [sigV]

theorem fixed_incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hv : IsFieldAt I v)
    (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) (hx : sigV I v x = x) :
    ∃ p, x = incL I v p := by
  obtain ⟨θ, hθ⟩ := exists_nonfixed I
  obtain ⟨p, q, rfl⟩ := decompV I v θ hθ x
  refine ⟨p, ?_⟩
  have : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hsig : I.cm.sig θ = star θ := rfl
  have hs : sigV I v (p ⊗ₜ 1 + q ⊗ₜ θ) = p ⊗ₜ 1 + q ⊗ₜ star θ := by
    simp [sigV, hsig]
  have hq : q ⊗ₜ[I.F] (θ - star θ) = 0 := by
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    have h2 := hx
    rw [hs] at h2
    exact (add_left_cancel h2).symm
  have hu : θ - star θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hq1 : incL I v q = 0 := by
    rw [incL_apply]
    calc q ⊗ₜ[I.F] (1 : I.E)
        = (q ⊗ₜ[I.F] (θ - star θ)) * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (θ - star θ)⁻¹) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hu]
      _ = 0 := by rw [hq, zero_mul]
  have hq0 : q = 0 := (incL I v).injective (hq1.trans (map_zero _).symm)
  rw [hq0, TensorProduct.zero_tmul, add_zero, incL_apply]

theorem trace_integral' : TraceInt := by
  intro I v hv α hα
  have : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hinv : ∀ y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v (sigV I v y) = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a e =>
      have h1 : ∀ e' : I.E, I.cm.sig e' = star e' := fun _ => rfl
      simp [sigV, h1]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  obtain ⟨τ, hτ⟩ := fixed_incL I v hv (α + sigV I v α) (by rw [map_add (f := _), hinv, add_comm])
  by_cases hτi : τ ∈ v.adicCompletionIntegers I.F
  · exact ⟨τ, hτi, hτ⟩

  have key : ∀ r₀ : v.adicCompletion I.F, α = incL I v r₀ →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t := by
    rintro r₀ rfl
    have h1 : incL I v (r₀ * r₀) = incL I v 1 := by
      rw [map_mul, map_one, ← hα, sigV_incL]
    have hr0 : r₀ * r₀ = 1 := (incL I v).injective h1
    have hmem : r₀ ∈ v.adicCompletionIntegers I.F := by
      rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers I.F) r₀ with h | h
      · exact h
      · rwa [inv_eq_of_mul_eq_one_right hr0] at h
    exact ⟨r₀ + r₀, add_mem hmem hmem, by rw [sigV_incL, map_add (f := _)]⟩
  have hdom : ∀ x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, x * y = 0 → x = 0 ∨ y = 0 := by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨b, hb⟩ := hv.mul_inv_cancel hx
      right
      calc y = (x * b) * y := by rw [hb, one_mul]
        _ = b * (x * y) := by ring
        _ = 0 := by rw [hxy, mul_zero]
  have hτinv : τ⁻¹ ∈ v.adicCompletionIntegers I.F :=
    (ValuationSubring.mem_or_inv_mem _ τ).resolve_left hτi
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hτi (zero_mem _)
  set s : v.adicCompletionIntegers I.F := ⟨τ⁻¹ * τ⁻¹, mul_mem hτinv hτinv⟩ with hs
  have hsK : (s : v.adicCompletion I.F) = τ⁻¹ * τ⁻¹ := rfl
  have hsm : s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers I.F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hτi
    have h1 : ((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) * s = 1 := by
      rw [← hu, Units.inv_mul]
    have h3 := congrArg (v.adicCompletionIntegers I.F).subtype h1
    rw [map_mul, map_one] at h3
    change (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
      v.adicCompletion I.F) * (τ⁻¹ * τ⁻¹) = 1 at h3
    have hw : (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) = τ * τ := by
      field_simp at h3
      linear_combination h3
    have hτeq : τ = (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) * τ⁻¹ := by
      rw [hw]
      field_simp
    rw [hτeq]
    exact mul_mem (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F)).2 hτinv
  let K := v.adicCompletion I.F
  let O := ↥(v.adicCompletionIntegers I.F)
  let w : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let m := IsLocalRing.maximalIdeal O
  have hcomplete : IsAdicComplete m O := by
    have hIntegers := Formalism.BasicNotions.Examples₂.adicInt_integers (K := I.F) v
    obtain ⟨π, hπ⟩ := Formalism.BasicNotions.Examples₂.adicInt_exists_unif (K := I.F) v
    have hm : m = Ideal.span {π} := by
      ext x
      change x ∈ IsLocalRing.maximalIdeal _ ↔ x ∈ Ideal.span {π}
      rw [Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff v x,
        Ideal.mem_span_singleton, hIntegers.dvd_iff_le]
      change Valued.v (x : K) < 1 ↔ Valued.v (x : K) ≤ Valued.v (π : K)
      rw [hπ]
      exact Formalism.BasicNotions.Examples₂.wz_lt_one_iff _
    have hpow (n : ℕ) (x : O) : x ∈ m ^ n ↔ w (x : K) ≤ w ((π : K) ^ n) := by
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hIntegers.dvd_iff_le]
      rfl
    have hAdic : IsAdic m := by
      rw [isAdic_iff]
      constructor
      · intro n
        have hπ0 : (π : K) ≠ 0 := by
          apply (map_ne_zero w).mp
          change Valued.v (π : K) ≠ 0
          rw [hπ]
          exact WithZero.exp_ne_zero
        have hopen := Valued.isOpen_closedBall K
          (r := w.restrict ((π : K) ^ n)) ((map_ne_zero w.restrict).mpr (pow_ne_zero n hπ0))
        convert hopen.preimage (continuous_subtype_val : Continuous (fun x : O => (x : K))) using 1
        ext x
        exact (hpow n x).trans (w.restrict_le_iff).symm
      · intro U hU
        rw [show nhds (0 : O) = Filter.comap (fun x : O => (x : K)) (nhds (0 : K)) from
          nhds_subtype_eq_comap] at hU
        obtain ⟨γ, -, hγ⟩ :=
          ((Valued.hasBasis_nhds_zero K (WithZero (Multiplicative ℤ))).comap _).mem_iff.mp hU
        have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by
          exact (_root_.map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
        obtain ⟨n, hn⟩ := Formalism.BasicNotions.Examples₂.wz_exists_nat_lt _ hγ0
        have hπn : w ((π : K) ^ n) = WithZero.exp (-(n : ℤ)) := by
          change Valued.v ((π : K) ^ n) = _
          rw [map_pow, hπ, ← WithZero.exp_nsmul]
          simp
        refine ⟨n, fun x hx => hγ ?_⟩
        apply w.restrict_lt_iff_lt_embedding.mpr
        refine ((hpow n x).mp hx).trans_lt ?_
        rwa [hπn]
    exact hAdic.isAdicComplete_iff.mpr
      ⟨completeSpace_coe_iff_isComplete.mpr (Valued.isClosed_valuationSubring K).isComplete,
        inferInstance⟩
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := m)
    (Polynomial.X ^ 2 + (Polynomial.C s - Polynomial.X)) (by monicity!) 0
    (by simpa [m] using hsm) (by simp)
  have ha2 : a ^ 2 + (s - a) = 0 := by simpa using ha
  have haK : (a : v.adicCompletion I.F) ^ 2 + (τ⁻¹ * τ⁻¹ - a) = 0 := by
    have h := congrArg (v.adicCompletionIntegers I.F).subtype ha2
    rw [map_add (f := _), map_pow, map_sub, map_zero] at h
    exact h
  have hr : (τ * a) * (τ - τ * a) = 1 := by
    have e1 : (a : v.adicCompletion I.F) - a ^ 2 = τ⁻¹ * τ⁻¹ := by linear_combination -haK
    calc (τ * a) * (τ - τ * a) = τ * τ * ((a : v.adicCompletion I.F) - a ^ 2) := by ring
      _ = τ * τ * (τ⁻¹ * τ⁻¹) := by rw [e1]
      _ = 1 := by field_simp
  have e2 : incL I v (τ * a) * incL I v (τ - τ * a) = 1 := by
    rw [← map_mul, hr, map_one]
  have e3 : incL I v (τ * a) + incL I v (τ - τ * a) = α + sigV I v α := by
    rw [← map_add (f := _), show τ * a + (τ - τ * a) = τ by ring, hτ]
  have hprod : (α - incL I v (τ * a)) * (α - incL I v (τ - τ * a)) = 0 := by
    linear_combination (-α) * e3 + e2 - hα
  rcases hdom _ _ hprod with h | h
  · exact key _ (sub_eq_zero.1 h)
  · exact key _ (sub_eq_zero.1 h)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

