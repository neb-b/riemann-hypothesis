module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormMulFibreVolume
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2.BaseVol

open GlobalTheory.LocFub.TopDens (dens_smul dens_add dens_zero)

variable {n d : ℕ} {J : Type}

theorem pull_bsL_dz (ε : Fin n ≃ Fin d ⊕ J) (a : Fin d) :
    pull (bsL ε) (dz a) = dz (ε.symm (.inl a)) ∧ pull (bsL ε) (dzb a) = dzb (ε.symm (.inl a)) := by
  rw [(pull_dz _ a).1, (pull_dz _ a).2]
  simp [bsL_apply, coordVec, PiLp.single_apply]

theorem pull_bsL_prod (ε : Fin n ≃ Fin d ⊕ J) (s : Finset (Fin d)) :
    pull (bsL ε) ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev d) : Alt d) =
      ((∏ a ∈ s, (Complex.I / 2) • sym (ε.symm (.inl a), ε.symm (.inl a)) : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]
    congr 1
    simp [sym, (pull_bsL_dz ε a).1, (pull_bsL_dz ε a).2]

theorem prod_mem (g : J → Fin n) (s : Finset J) :
    ((∏ j ∈ s, (Complex.I / 2) • sym (g j, g j) : Ev n) : Alt n) ∈ ⋀[ℂ]^(2 * s.card) (Fin n ⊕ Fin n → ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subalgebra.coe_mul, Finset.card_insert_of_notMem ha,
      show 2 * (s.card + 1) = 1 + 1 + 2 * s.card by ring]
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ih
    rw [Subalgebra.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    change dz (g a) * dzb (g a) ∈ _
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ?_
    · simp [dz, ExteriorAlgebra.exteriorPower]
    · simp [dzb, ExteriorAlgebra.exteriorPower]

theorem dens_pull_bas [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) {T : Finset (Fin (d + d))} (hT : T ≠ Finset.univ) :
    dens (pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = 0 := by
  have hc : T.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
  have hn : n = d + Fintype.card J := by simpa using Fintype.card_congr ε
  have hm : pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) ∈
      ⋀[ℂ]^(T.card + 2 * (Finset.univ : Finset J).card) (Fin n ⊕ Fin n → ℂ) := by
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ (prod_mem _ _)
    rw [bas, ExteriorAlgebra.basis_apply _ T, CxForm.pull, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact Subtype.property _
  have := GlobalTheory.PullTop.repr_eq_zero_of_card_ne
    ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  rw [dens]
  exact div_eq_zero_iff.2 (Or.inl this)

theorem pull_vol_mul [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) :
    pull (bsL ε) (vol d : Alt d) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) = (vol n : Alt n) := by
  rw [vol, pull_bsL_prod, ← Subalgebra.coe_mul, vol, ← ε.symm.prod_comp, Fintype.prod_sum_type]

theorem dens_pull_mul_vol : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  intro n d J _ ε α
  have hα : α ∈ Submodule.span ℂ (Set.range (bas d)) := by rw [(bas d).span_eq]; trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    by_cases hT : T = Finset.univ
    · obtain ⟨c, hc, e⟩ := vol_eq d
      have e' : bas d T = c⁻¹ • (vol d : Alt d) := by rw [e, hT, inv_smul_smul₀ hc]
      rw [e', map_smul, smul_mul_assoc, dens_smul, dens_smul, dens_vol, pull_vol_mul, dens_vol]
    · rw [dens_pull_bas ε hT]
      simp [dens, hT]
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, dens_add, dens_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx]

end GlobalTheory.FlagCell2.BaseVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBlockTriangularDiagonalBlocks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagTri

theorem eval_zero_of_const {A : Type} [CommRing A] [Algebra ℂ A] (l : A →ₗ[ℂ] ℂ) (Q : Polynomial A) (c : ℂ)
    (h : ∀ x : ℂ, x ≠ 0 → l (Q.eval (algebraMap ℂ A x)) = c) : l (Q.eval (algebraMap ℂ A 0)) = c := by
  have hc : Continuous fun x : ℂ => l (Q.eval (algebraMap ℂ A x)) := by
    clear h
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, map_add (f := _)]; exact hp.add hq
    | monomial k a =>
      have : (fun x : ℂ => l ((Polynomial.monomial k a).eval (algebraMap ℂ A x))) = fun x => x ^ k * l a := by
        funext x
        rw [Polynomial.eval_monomial, ← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [this]
      fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc (continuous_const (y := c)) (fun x hx => h x hx)
  exact congrFun this 0

variable {n : ℕ}

def scale (c : Fin n → ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.diagonal (Sum.elim c c)))

theorem dens_scale (c : Fin n → ℂ) (β : Alt n) : dens (scale c β) = (∏ a, c a) ^ 2 * dens β := by
  simp only [dens, scale, bas]
  rw [exterior_repr_univ_map, LinearMap.det_toLin', Matrix.det_diagonal, Fintype.prod_sum_type, mul_div_assoc, sq]
  rfl

theorem scale_dz (c : Fin n → ℂ) (a : Fin n) : scale c (dz a) = c a • dz a ∧ scale c (dzb a) = c a • dzb a := by
  simp only [dz, dzb, ← map_smul]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    by_cases h : b = a <;> simp [Matrix.mulVec_diagonal, Pi.single_apply, h]

theorem scale_sym (c : Fin n → ℂ) (a b : Fin n) :
    scale c (sym (a, b) : Ev n) = (c a * c b) • ((sym (a, b) : Ev n) : Alt n) := by
  change scale c (dz a * dzb b) = (c a * c b) • (dz a * dzb b)
  rw [map_mul, (scale_dz c a).1, (scale_dz c b).2, smul_mul_smul_comm]

theorem scale_pull {d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (c : Fin n → ℂ) (hc : ∀ a, c (ε.symm (.inl a)) = 1)
    (α : Alt d) : scale c (pull (bsL ε) α) = pull (bsL ε) α := by
  have key (a : Fin d) (b : Fin n) : c b * bsL ε (coordVec b) a = bsL ε (coordVec b) a ∧
      c b * (starRingEnd ℂ) (bsL ε (coordVec b) a) = (starRingEnd ℂ) (bsL ε (coordVec b) a) := by
    rw [bsL_apply]
    by_cases h : ε.symm (.inl a) = b
    · subst h
      simp [hc]
    · simp [coordVec, h]
  rw [scale, pull, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
  congr 3
  ext (i | i) (j | j) <;> simp [Matrix.diagonal_mul, key]

theorem map_prod_pow {T : Type} (φ : Alt n →ₐ[ℂ] Alt n) (x y : T → Ev n) (r : T → ℕ)
    (h : ∀ t, φ (x t) = y t) (s : Finset T) :
    φ ((∏ t ∈ s, x t ^ r t : Ev n) : Alt n) = ((∏ t ∈ s, y t ^ r t : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih,
      Subalgebra.coe_pow, Subalgebra.coe_pow, map_pow, h]

theorem dens_blockTri : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  intro n d J T _ _ ε lev ρ K r hr hK α
  let wt : Fin n → ℕ := fun a => (ε a).elim (fun _ => 0) fun j => ρ (lev j) + 1
  have w0 (a) : wt (ε.symm (.inl a)) = 0 := by simp [wt]
  have w1 (j) : wt (ε.symm (.inr j)) = ρ (lev j) + 1 := by simp [wt]
  have hw (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) :
      wt a < ρ t + 1 ∨ ∃ j : {j // lev j = t}, ε.symm (.inr j.1) = a := by
    obtain ⟨a | j, rfl⟩ := ε.symm.surjective a
    · left; rw [w0]; omega
    · by_cases e : lev j = t
      · exact .inr ⟨⟨j, e⟩, rfl⟩
      · left
        rw [w1]
        by_contra hn
        obtain ⟨b, hb⟩ := h
        have := hK t j e (by omega) b
        tauto
  have hw' (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) : wt a ≤ ρ t + 1 := by
    rcases hw t a h with h | ⟨j, rfl⟩
    · omega
    · rw [w1, j.2]
  let l : Ev n →ₗ[ℂ] ℂ :=
    { toFun := fun x => dens (pull (bsL ε) α * (x : Alt n))
      map_add' := fun x y => by simp [dens, mul_add, add_div]
      map_smul' := fun c x => by simp [dens, mul_div_assoc] }
  have hl (x : Ev n) : l x = dens (pull (bsL ε) α * (x : Alt n)) := rfl
  let e : T → Fin n → Fin n → ℕ := fun t a b => (ρ t + 1 - wt a) + (ρ t + 1 - wt b)
  let Q : Polynomial (Ev n) := ∏ t, (∑ a, ∑ b, Polynomial.monomial (e t a b) (K t a b • sym (a, b))) ^ r t
  have hQ (x : ℂ) : Q.eval (algebraMap ℂ (Ev n) x) =
      ∏ t, (∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) ^ r t := by
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← map_pow, mul_comm, ← Algebra.smul_def, smul_smul]
  rw [← hl, ← hl, ← eval_zero_of_const l Q (l (∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n)) ?_]
  · rw [hQ]
    refine congrArg l (Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_)
    have inj : Function.Injective fun j : {j // lev j = t} => ε.symm (.inr j.1) :=
      fun i j h => Subtype.ext (Sum.inr_injective (ε.symm.injective h))
    symm
    refine Fintype.sum_of_injective _ inj _ _ (fun a ha => Finset.sum_eq_zero fun b _ => ?_) fun a => ?_
    · by_cases h : K t a b = 0
      · simp [h]
      · rcases hw t a ⟨b, .inl h⟩ with h' | h'
        · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
        · exact absurd h' ha
    · refine Fintype.sum_of_injective _ inj _ _ (fun b hb => ?_) fun b => ?_
      · by_cases h : K t (ε.symm (.inr a.1)) b = 0
        · simp [h]
        · rcases hw t b ⟨_, .inr h⟩ with h' | h'
          · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
          · exact absurd h' hb
      · simp [e, w1, a.2, b.2]
  · intro x hx
    have h1 := dens_scale (fun a => x⁻¹ ^ wt a)
      (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n))
    rw [map_mul, scale_pull ε _ (fun a => by simp [w0]),
      map_prod_pow _ _ (fun t => (x⁻¹ ^ (ρ t + 1)) ^ 2 • ∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) r ?_,
      ← hl, ← hl] at h1
    · have h2 : ∏ a, x⁻¹ ^ wt a = ∏ t, (x⁻¹ ^ (ρ t + 1)) ^ r t := by
        rw [← ε.symm.prod_comp, Fintype.prod_sum_type]
        simp only [w0, w1, pow_zero, Finset.prod_const_one, one_mul]
        rw [← Fintype.prod_fiberwise lev]
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [Finset.prod_congr rfl (g := fun _ => x⁻¹ ^ (ρ t + 1)) fun j _ => by rw [j.2], Finset.prod_const, hr]
        simp
      simp only [smul_pow, Finset.prod_smul] at h1
      rw [map_smul, ← hQ, h2, ← Finset.prod_pow, smul_eq_mul] at h1
      simp only [← pow_mul, mul_right_comm _ (r _) 2] at h1
      refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (inv_ne_zero hx)) h1
    · intro t
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, map_sum, map_smul, scale_sym, Finset.smul_sum,
        smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      by_cases h : K t a b = 0
      · simp [h]
      · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le (hw' t a ⟨b, .inl h⟩)
        obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hw' t b ⟨a, .inr h⟩)
        have : e t a b = p + q := by simp only [e]; omega
        rw [this, sq]
        nth_rw 1 [hp]
        rw [hq]
        simp only [inv_pow]
        field_simp
        ring

end GlobalTheory.FlagTri
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensity
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun y => C c * X y) Q) d = c ^ (d.sum fun _ e => e) * AddMonoidAlgebra.coeff Q d := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
      map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens


open GlobalTheory.ChernTopDens in
theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, _root_.GlobalTheory.ChernCalc.DensTop.dens_aeval_sym, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem topologicalKrullDim_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  intro K _ A
  haveI : Nonempty A.X.left := ⟨A.origin⟩
  exact GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.X.hom A.dim A.smooth

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionEqTorusPointAtClosedPointFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

theorem GlobalTheory.ToricTorsionClosedPt.main : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz
  have hk0 : k ≠ 0 := by omega
  let u : Vˣ := Units.ofPowEqOne w k hw hk0
  have hu : (u : V) = w := Units.val_ofPowEqOne w k hw hk0
  have huk : u ^ k = 1 := Units.pow_ofPowEqOne hw hk0
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτVv : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hτVv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huk, one_zpow]
  have powk : ∀ {L : Type} [Field L] (t : Multiplicative D.toPre.X →* Lˣ) (y : L), y ^ k = 1 →
      (∀ χ, (t (Multiplicative.ofAdd χ) : L) = y ^ c χ) → t ^ k = 1 := by
    intro L _ t y hy ht
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
      ← ofAdd_toAdd χ, ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have mapv : ∀ {L : Type} [Field L] (f : V →+* L) (χ : Multiplicative D.toPre.X),
      f (τV χ : V) = f w ^ c (Multiplicative.toAdd χ) := by
    intro L _ f χ
    rw [hτVv, ← hu]
    show ((Units.map (f : V →* L) (u ^ c (Multiplicative.toAdd χ)) : Lˣ) : L) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  let sV := s V (RingHom.id V) τV hτV
  let σ₁ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (by rw [hσ, Category.id_comp])
  have hσ₁β : σ₁ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₁G : σ₁ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  have hsVG : sV.left ≫ G.hom = 𝟙 _ := by
    rw [Over.w sV]
    show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
    exact Spec.map_id _

  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := by
    dsimp only [a, spMap, jK]
    rw [← Spec.map_comp]
    rfl
  have haI : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI : IsDominant (spMap a) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 haI]; exact bot_le)⟩
  haveI : IsSeparated G.hom := hG.separated
  obtain ⟨τF, q, hτF, hq, hqt, hqx⟩ := hx
  have hτFk : τF ^ k = 1 := powk τF _ (by rw [← map_pow, ← map_pow, hw, map_one, map_one]) hτF
  have e4 := s4 F a τF hτFk q x rfl hq hqt hqx
  have e2 := s2 V F (RingHom.id V) a a τV hτV τF hτFk (RingHom.comp_id a).symm (fun χ => by
    rw [mapv a χ]; exact hτF (Multiplicative.toAdd χ))
  change _ = spMap a ≫ sV.left at e2
  have hi : σ₁ = sV.left := by
    refine ext_of_isDominant_of_isSeparated G.hom (hσ₁G.trans hsVG.symm) (spMap a) ?_
    refine hβ.1.hom_ext ?_ ?_
    · have l : spMap a ≫ σ₁ ≫ β = x.left ≫ genMap U ≫ β := by
        rw [hσ₁β, hxσ, ha, Category.assoc]
      have r : spMap a ≫ sV.left ≫ β = x.left ≫ genMap U ≫ β := by
        rw [← Category.assoc, ← e2, ← e4, Category.assoc]
      rw [Category.assoc, Category.assoc, l, r]
    · simp only [Category.assoc]
      exact congrArg (spMap a ≫ ·) (hσ₁G.trans hsVG.symm)
  have hτk : τ ^ k = 1 := powk τ (b w) (by rw [← map_pow, hw, map_one]) hτ
  have e2' := s2 V κ (RingHom.id V) b b τV hτV τ hτk (RingHom.comp_id b).symm (fun χ => by
    rw [mapv b χ]; exact hτ (Multiplicative.toAdd χ))
  have e3 := s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z (RingHom.id_comp b).symm hz
  rw [← hσ₁β, hi, ← Category.assoc, ← e2', e3, Category.assoc]

end
end

