module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacter
section
open MvPolynomial

namespace GlobalTheory.HTCPoly

theorem prod_zpow_eq {ι G : Type} [CommGroup G] (u : G) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, u ^ a i = u ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]

def wt (k : n → ℤ) (m : (n × n) →₀ ℕ) : ℤ := ∑ i : n × n, (m i : ℤ) * k i.2

theorem unit_prod (k : n → ℤ) (u : Cˣ) (m : (n × n) →₀ ℕ) :
    ∏ i : n × n, ((u ^ k i.2 : Cˣ) : C) ^ (m i) = ((u ^ wt k m : Cˣ) : C) := by
  have h : ∏ i : n × n, (u ^ k i.2) ^ (m i) = u ^ wt k m := by
    rw [wt, ← prod_zpow_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [← h, Units.coe_prod]
  simp [Units.val_pow_eq_pow_val]

theorem eval_eq_sum {σ : Type} [Fintype σ] (x : σ → C) (p : MvPolynomial σ C)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    eval x p = ∑ m ∈ s, AddMonoidAlgebra.coeff p m * ∏ i, x i ^ m i := by
  rw [eval_eq']
  refine Finset.sum_subset hs fun m _ hm => ?_
  have : AddMonoidAlgebra.coeff p m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [this, zero_mul]

theorem eval_mul_diag (k : n → ℤ) (u : Cˣ) (y : Matrix n n C) (p : MvPolynomial (n × n) C)
    (s : Finset ((n × n) →₀ ℕ)) (hs : p.support ⊆ s) :
    eval (fun ij => (y * Matrix.diagonal (fun j => ((u ^ k j : Cˣ) : C))) ij.1 ij.2) p
      = ∑ m ∈ s, ((u ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff p m * ∏ i : n × n, y i.1 i.2 ^ m i := by
  rw [eval_eq_sum _ _ s hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [Matrix.mul_diagonal, mul_pow, Finset.prod_mul_distrib, unit_prod]
  ring

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

def vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C) :
    Submodule C (((n × n) →₀ ℕ) →₀ C) where
  carrier := {φ | ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (a + b) : MvPolynomial (n × n) C) =
      AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b by simp, map_add (f := _), ha γ, hb γ, add_zero]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro c a ha γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (c • a) : MvPolynomial (n × n) C) =
      c • AddMonoidAlgebra.ofCoeff a by simp, smul_eval, ha γ, mul_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly
variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]
variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

theorem mem_vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C)
    (φ : ((n × n) →₀ ℕ) →₀ C) :
    φ ∈ vanJ ρ P ↔ ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0 := Iff.rfl

theorem vanJ_stable (χ : Γ →* Cˣ) (ρ : Γ →* Matrix.GeneralLinearGroup n C)
    (hfix : ∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j)
    (P : Matrix n n C) (k : n → ℤ)
    (hP : ∀ g : Γ, (ρ g : Matrix n n C) * P.map (fun a => g • a) =
      P * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) :
    ∀ g : Γ, ∀ φ ∈ vanJ ρ P, ∃ ψ ∈ vanJ ρ P,
      ∀ m, ψ m = ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) := by
  intro g φ hφ
  refine ⟨Finsupp.onFinset φ.support (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) ?_, ?_,
    fun m => Finsupp.onFinset_apply⟩
  · intro m hm
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hm
    rw [h0, smul_zero, mul_zero]
  · rw [mem_vanJ] at hφ ⊢
    intro γ
    set σg := MulSemiringAction.toRingHom Γ C g
    set p : MvPolynomial (n × n) C := AddMonoidAlgebra.ofCoeff φ
    have hfix' : (ρ (γ * g) : Matrix n n C).map σg = ρ (γ * g) := by
      ext i j
      exact hfix g (γ * g) i j
    have key : (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C)) =
        ((ρ (γ * g) : Matrix n n C) * P).map σg := by
      calc (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))
          = (ρ γ : Matrix n n C) * (P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))) :=
            Matrix.mul_assoc _ _ _
        _ = (ρ γ : Matrix n n C) * ((ρ g : Matrix n n C) * P.map (fun a => g • a)) := by rw [hP g]
        _ = ((ρ (γ * g) : Matrix n n C) * P).map σg := by
            rw [Matrix.map_mul, hfix', map_mul, Units.val_mul, Matrix.mul_assoc]
            rfl
    have e1 : eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
        (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset φ.support
          (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) (by
            intro m hm
            rw [Finsupp.mem_support_iff]
            intro h0
            apply hm
            rw [h0, smul_zero, mul_zero])) : MvPolynomial (n × n) C)
        = ∑ m ∈ φ.support, ((χ g ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff (map σg p) m *
            ∏ i : n × n, ((ρ γ : Matrix n n C) * P) i.1 i.2 ^ m i := by
      refine (eval_eq_sum _ _ φ.support ?_).trans ?_
      · intro m hm
        rw [MvPolynomial.mem_support_iff] at hm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hm
        show ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) = 0
        rw [h0, smul_zero, mul_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_map]
      rfl
    rw [e1, ← eval_mul_diag k (χ g) _ (map σg p) φ.support (MvPolynomial.support_map_subset _ _), key]
    have h2 := eval₂_comp_left σg (RingHom.id C)
      (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
    rw [RingHom.comp_id] at h2
    rw [eval_map]
    calc eval₂ σg (fun ij : n × n => (((ρ (γ * g) : Matrix n n C) * P).map σg) ij.1 ij.2) p
        = σg (eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p) :=
          h2.symm
      _ = 0 := by
          rw [show eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
            = eval (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p from rfl, hφ (γ * g),
            map_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly

theorem vanish_at_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  intro C Γ n _ _ _ _ _ χ hT ρ hfix P k hP f hf t
  set Pm : Matrix n n C := (P : Matrix n n C) with hPm
  set Qm : Matrix n n C := ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C) with hQm
  have hPQ : Pm * Qm = 1 := by
    rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let q : n × n → MvPolynomial (n × n) C := fun ij => ∑ l, X (ij.1, l) * MvPolynomial.C (Qm l ij.2)
  have hφ : ∀ y : Matrix n n C, eval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      eval (fun ij : n × n => (y * Qm) ij.1 ij.2) f := by
    intro y
    show aeval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      aeval (fun ij : n × n => (y * Qm) ij.1 ij.2) f
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun F : n × n → C => aeval F f) (funext fun ij => ?_)
    simp [q, Matrix.mul_apply]
  set p : MvPolynomial (n × n) C := aeval q f with hp
  have hpJ : AddMonoidAlgebra.coeff p ∈ vanJ ρ Pm := by
    rw [mem_vanJ]
    intro γ
    show eval _ p = 0
    rw [hφ, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    exact hf γ
  have hgr := _root_.GlobalTheory.tate_weight_graded χ hT (wt k) (vanJ ρ Pm) (vanJ_stable χ ρ hfix Pm k hP) _ hpJ
  have hzero : ∀ d : ℤ, eval (fun ij : n × n => Pm ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter (fun m => wt k m = d)) :
        MvPolynomial (n × n) C) = 0 := by
    intro d
    have h1 := (mem_vanJ ρ Pm _).mp (hgr d) 1
    rwa [map_one, Units.val_one, Matrix.one_mul] at h1
  rw [← hφ (Pm * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)))]
  rw [eval_mul_diag k t Pm p p.support subset_rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (t := p.support.image (wt k)) (g := wt k)
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero ((t ^ d : Cˣ) : C), ← hzero d,
    eval_eq_sum _ _ (p.support.filter (fun m => wt k m = d)) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have hc : AddMonoidAlgebra.coeff (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter
        (fun m => wt k m = d)) : MvPolynomial (n × n) C) m = AddMonoidAlgebra.coeff p m :=
      Finsupp.filter_apply_pos _ _ hm.2
    rw [hc, hm.2]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at hm
    rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
    by_contra hne
    apply hm
    show (Finsupp.filter (fun m => wt k m = d) (AddMonoidAlgebra.coeff p)) m = 0
    by_cases hw : wt k m = d
    · rw [Finsupp.filter_apply_pos (fun m => wt k m = d) _ hw]
      by_contra h
      exact hne ⟨h, hw⟩
    · exact Finsupp.filter_apply_neg _ _ hw

end GlobalTheory.HTCPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusSurjective
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem valsAt_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype) := by
  intro G _ τ hττ T hT ι s w hsw hex r e he hs n
  choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)
  have hτ : ∀ i j, w (e i) (τ (y j)) = 1 := by
    intro i j
    have h1 : w (s (e i)) (y j) = 1 := hy2 j _ (hs i j)
    have a := (hsw (e i) (y j)).1 (by rw [h1]; simp)
    have b := (hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)
    rw [map_inv, map_inv, toAdd_inv] at b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    omega
  have hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T := by
    intro j
    rw [hT, map_mul, map_inv, hττ]
    group
  refine ⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply]
  rw [map_prod, toAdd_prod]
  have hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0 := by
    intro j
    rw [map_mul, map_inv, hτ, inv_one, mul_one]
    split_ifs with hij
    · subst hij; rw [hy1]; rfl
    · rw [hy2 j (e i) fun h => hij (he _ _ h)]; rfl
  simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UnitLemma
end

