module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibHess
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_hess

noncomputable def tl (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) (Fin.succ i)

theorem tl_apply (d : ℕ) (z : Fin (d + 1) → ℂ) : tl d z = Fin.tail z := rfl

theorem tl_cons (d : ℕ) (a : ℂ) (y : Fin d → ℂ) : tl d (Fin.cons a y) = y := by
  ext i; simp [tl]

theorem tl_zero (d : ℕ) : tl d (Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_zero' (d : ℕ) : tl d (Complex.I • Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_succ (d : ℕ) (j : Fin d) : tl d (Pi.single j.succ 1) = Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem tl_succ' (d : ℕ) (j : Fin d) :
    tl d (Complex.I • Pi.single j.succ 1) = Complex.I • Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem xi_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) :
    xiPot G a = -Real.log ((G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re)
      + (1 / 2) * Real.log ((G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im) := by
  have h1 : (herm2 G ![1, a] ![1, a]).re = (G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re := by
    simp [herm2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have h2 : G.det.re = (G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im := by
    simp [Matrix.det_fin_two]
    ring
  rw [xiPot, h1, h2]

theorem jet (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (h1 : G y = 1)
    (h0 : ∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) (a : ℂ)
    (A B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ)
    (hA : ∀ p q, A p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).re)) y)
    (hB : ∀ p q, B p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).im)) y) :
    ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧
    ∀ u v, fderiv ℝ (fderiv ℝ (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)))
        (Fin.cons a y) u v =
      -((1 + (a.re ^ 2 + a.im ^ 2))⁻¹ * (A 0 0 (tl d u) (tl d v)
          + a.re * (A 0 1 (tl d u) (tl d v) + A 1 0 (tl d u) (tl d v))
          + a.im * (B 1 0 (tl d u) (tl d v) - B 0 1 (tl d u) (tl d v))
          + (a.re ^ 2 + a.im ^ 2) * A 1 1 (tl d u) (tl d v)
          + 2 * ((u 0).re * (v 0).re + (u 0).im * (v 0).im))
        - (2 * a.re * (u 0).re + 2 * a.im * (u 0).im) * (2 * a.re * (v 0).re + 2 * a.im * (v 0).im)
          / (1 + (a.re ^ 2 + a.im ^ 2)) ^ 2)
        + (1 / 2) * (A 0 0 (tl d u) (tl d v) + A 1 1 (tl d u) (tl d v)) := by
  have hT : tl d (Fin.cons a y) = y := tl_cons d a y
  have hJ : ∀ (l : ℂ →L[ℝ] ℝ) (p q : Fin 2), J (fun z : Fin (d + 1) → ℂ => l (G (tl d z) p q))
      (Fin.cons a y) (l (G y p q)) (fun _ => 0)
      (fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y (tl d u) (tl d w)) := by
    intro l p q
    refine J.comp (tl d) (f := fun y' => l (G y' p q)) (v := l (G y p q)) (L := fun _ => 0)
      (B := fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y u w) ?_
    rw [hT]
    exact J.atom (hC p q) (h0 p q) l
  have hRe : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.reCLM (G (tl d z) p q))
      (Fin.cons a y) (if p = q then 1 else 0) (fun _ => 0) (fun u w => A p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.reCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [h, Matrix.one_apply_ne h]
    · intro u w
      rw [hA]
      rfl
  have hIm : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.imCLM (G (tl d z) p q))
      (Fin.cons a y) 0 (fun _ => 0) (fun u w => B p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.imCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
    · intro u w
      rw [hB]
      rfl
  have hx : J (fun z : Fin (d + 1) → ℂ => (Complex.reCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.re (fun u => (u 0).re) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have hw : J (fun z : Fin (d + 1) → ℂ => (Complex.imCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.im (fun u => (u 0).im) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have key := main_jet hx hw (by simpa using hRe 0 0) (by simpa using hRe 0 1)
    (by simpa using hRe 1 0) (by simpa using hRe 1 1) (hIm 0 0) (hIm 0 1) (hIm 1 0) (hIm 1 1)
    (φ := fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (fun z => by
      simp only [tl_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, ContinuousLinearMap.proj_apply]
      exact xi_eq _ _)
  exact key

noncomputable def hm {d : ℕ} (H : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin d) (Fin d) ℂ := fun i j =>
  ((H (Pi.single i 1) (Pi.single j 1)
      + H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
    Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1)
      - H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4

end PositivityTheory.Xgp.fib_hess
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibMdisc
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_mdisc

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix

theorem fac_cancel (n : ℕ) (S : ℂ) : (n.factorial : ℂ) * ((1 / (n.factorial : ℂ)) * S) = S := by
  rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast n.factorial_ne_zero), one_mul]

theorem det_block {d : ℕ} (c : ℂ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (h0 : M 0 0 = c) (hcol : ∀ i : Fin d, M i.succ 0 = 0) :
    M.det = c * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h0, hcol]

noncomputable def phi {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) :=
  x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2)

theorem phi_zero {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : phi x 0 = x.1 := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem phi_succ {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) (j : Fin d) :
    phi x j.succ = x.1.succAbove (x.2 j) := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

theorem phi_bijective (d : ℕ) : Function.Bijective (phi (d := d)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have h0 : r = r' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (d + 1)) => σ 0) h
      simpa [phi_zero] using this
    subst h0
    have h1 : Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ) =
        Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ') := mul_left_cancel h
    have := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]

theorem part1 (d : ℕ) (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ) :
    ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) =>
      Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) =
      ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s)) := by
  classical
  simp only [mdisc_eq_sum_perm, fac_cancel]
  have hterm : ∀ σ : Equiv.Perm (Fin (d + 1)),
      (Matrix.of fun i j => (Matrix.of fun p q : Fin (d + 1) =>
        Fin.cases (Fin.cases (f (σ j)) (fun _ => 0) q)
          (fun p' => Fin.cases 0 (fun q' => Bm (σ j) p' q') q) p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j).det =
        f (σ 0) * (Matrix.of fun i j => Bm (σ j.succ) i j).det := by
    intro σ
    rw [det_block (f (σ 0))]
    · congr 1
    · simp
    · intro i; simp
  simp only [hterm]
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective phi (phi_bijective d) _ _ fun x => ?_
  simp only [phi_zero, phi_succ]

end PositivityTheory.Xgp.fib_mdisc

theorem PositivityTheory.Xgp.t_fib_mdisc : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  intro d
  refine ⟨PositivityTheory.Xgp.fib_mdisc.part1 d, ?_⟩
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  exact ⟨M, fun Bm => by rw [hM], fun π Bm => by rw [hM, ReciprocityTheory.AnForm.A.mdisc_comp_perm]⟩
end

