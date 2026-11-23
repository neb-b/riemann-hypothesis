module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeOfXRegularQuotientTorsionFreeScalarTower
section
namespace GlobalTheory

open PowerSeries

theorem free_of_X_regular_quotient_torsionFree_scalarTower (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M] [Module O M] [IsScalarTower O (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  classical
  set p : Submodule (PowerSeries O) M :=
    Ideal.span {(PowerSeries.X : PowerSeries O)} • (⊤ : Submodule (PowerSeries O) M) with hp
  have memp : ∀ m : M, m ∈ p ↔ ∃ y : M, m = (PowerSeries.X : PowerSeries O) • y := by
    intro m
    rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Submodule.mem_top, hy.symm⟩
  have hsmul : ∀ (c : O) (m : M), c • m = (PowerSeries.C c : PowerSeries O) • m := by
    intro c m
    rw [← IsScalarTower.algebraMap_smul (PowerSeries O) c m, PowerSeries.algebraMap_apply]
    simp

  have hdec : ∀ r : PowerSeries O, ∃ s : PowerSeries O,
      r = PowerSeries.C (PowerSeries.constantCoeff r) + PowerSeries.X * s := by
    intro r
    obtain ⟨s, hs⟩ : (PowerSeries.X : PowerSeries O) ∣
        r - PowerSeries.C (PowerSeries.constantCoeff r) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    exact ⟨s, by rw [← hs]; ring⟩

  have hN : ∀ (r : PowerSeries O) (y : M ⧸ p), r • y = (PowerSeries.constantCoeff r) • y := by
    intro r y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    obtain ⟨s, hs⟩ := hdec r
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, memp]
    have e1 : r • m = (PowerSeries.C (PowerSeries.constantCoeff r) : PowerSeries O) • m
        + (PowerSeries.X : PowerSeries O) • (s • m) := by
      conv_lhs => rw [hs]
      rw [add_smul, mul_smul]
    refine ⟨s • m, ?_⟩
    rw [e1, hsmul]
    abel
  have hfin : Module.Finite O (M ⧸ p) := by
    obtain ⟨T, hT'⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (PowerSeries O) (M ⧸ p))
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro y -
    have hy : y ∈ Submodule.span (PowerSeries O) (T : Set (M ⧸ p)) := by
      rw [hT']
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [hN]
      exact Submodule.smul_mem _ _ hx
  have htf : Module.IsTorsionFree O (M ⧸ p) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c y hcy => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, memp, hsmul c m] at hcy
      rw [Submodule.Quotient.mk_eq_zero, memp]
      exact hT c m hc hcy
  let b := Module.Free.chooseBasis O (M ⧸ p)
  choose e he using fun i => Submodule.Quotient.mk_surjective p (b i)
  have hspan : (⊤ : Submodule (PowerSeries O) M) ≤ Submodule.span (PowerSeries O) (Set.range e) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {PowerSeries.X})
      (Module.finite_def.mp inferInstance) ?_ ?_
    · rw [Ideal.span_le]
      rintro _ rfl
      change PowerSeries.X ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries O))
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp
    · intro m _
      set c := b.repr (Submodule.Quotient.mk m)
      have h2 : m - ∑ i, c i • e i ∈ p := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply p (∑ i, c i • e i), map_sum]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, he]
        exact (b.sum_repr _).symm
      rw [Submodule.mem_sup]
      refine ⟨∑ i, c i • e i, ?_, m - ∑ i, c i • e i, h2, by abel⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (PowerSeries O) e := by
    rw [Fintype.linearIndependent_iff]

    have key : ∀ k : ℕ, ∀ g : Module.Free.ChooseBasisIndex O (M ⧸ p) → PowerSeries O,
        ∑ i, g i • e i = 0 → ∀ i, (PowerSeries.X : PowerSeries O) ^ k ∣ g i := by
      intro k
      induction k with
      | zero =>
        intro g _ i
        simp
      | succ k ih =>
        intro g hg i
        choose s hs using fun j => hdec (g j)
        have hc : ∀ j, PowerSeries.constantCoeff (g j) = 0 := by
          have h0 : ∑ j, (PowerSeries.constantCoeff (g j)) • b j = 0 := by
            have h1 := congrArg p.mkQ hg
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_smul, Submodule.mkQ_apply, he, hN, map_zero] at h1
            exact h1
          exact (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0
        have hgX : ∀ j, g j = PowerSeries.X * s j := by
          intro j
          rw [hs j, hc j]
          simp
        have hg' : (PowerSeries.X : PowerSeries O) • ∑ j, s j • e j = 0 := by
          rw [Finset.smul_sum, ← hg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hgX j, mul_smul]
        obtain ⟨t, ht⟩ := ih s (hX _ hg') i
        exact ⟨t, by rw [hgX i, ht]; ring⟩
    intro g hg i
    ext n
    have h := PowerSeries.X_pow_dvd_iff.mp (key (n + 1) g hg i) n (Nat.lt_succ_self n)
    simpa using h
  exact Module.Free.of_basis (Module.Basis.mk hli hspan)

theorem free_of_X_regular_of_quotient_torsionFree (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  let _ : Module O M := Module.compHom M (algebraMap O (PowerSeries O))
  have : IsScalarTower O (PowerSeries O) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact free_of_X_regular_quotient_torsionFree_scalarTower O M hX hT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
section
namespace GlobalTheory.FrobeniusDefect

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

theorem nzd_mul {a b : R} (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0) :
    ∀ x : R, (a * b) * x = 0 → x = 0 :=
  fun x h => hb x (ha _ (by rw [← mul_assoc]; exact h))

theorem nzd_pow {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) :
    ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → x = 0
  | 0 => fun x h => by simpa using h
  | n + 1 => by rw [pow_succ]; exact nzd_mul (nzd_pow ha n) ha

theorem nzd_unit {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) (v : Rˣ) :
    ∀ x : R, (a * v) * x = 0 → x = 0 :=
  nzd_mul ha (fun x h => by simpa using congrArg (fun y => (↑v⁻¹ : R) * y) h)

theorem smul_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M N : Matrix (Fin d) (Fin d) R} (h : c • M = c • N) : M = N := by
  ext i j
  have := congrArg (fun P => P i j) h
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.mp (hc _ (by rw [mul_sub, this, sub_self]))

theorem mul_left_of {c : R} {P P' : Matrix (Fin d) (Fin d) R} (h : P * P' = c • 1)
    (X : Matrix (Fin d) (Fin d) R) : P * (P' * X) = c • X := by
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul]

theorem left_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {P P' : Matrix (Fin d) (Fin d) R} (h : P' * P = c • 1)
    {X Y : Matrix (Fin d) (Fin d) R} (hXY : P * X = P * Y) : X = Y :=
  smul_cancel hc (by rw [← mul_left_of h X, ← mul_left_of h Y, hXY])

theorem mul_comm_of_nzd {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M M' : Matrix (Fin d) (Fin d) R} (h : M * M' = c • 1) : M' * M = c • 1 := by
  have hdet : M.det * M'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdM : ∀ x : R, M.det * x = 0 → x = 0 := fun x hx =>
    nzd_pow hc d x (by rw [← hdet, mul_comm M.det, mul_assoc, hx, mul_zero])
  have h0 : M * (M' * M - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have h1 : M.det • (M' * M - c • 1) = M.det • (0 : Matrix (Fin d) (Fin d) R) := by
    calc M.det • (M' * M - c • 1)
          = (M.det • (1 : Matrix (Fin d) (Fin d) R)) * (M' * M - c • 1) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * M * (M' * M - c • 1) := by rw [Matrix.adjugate_mul]
      _ = M.det • (0 : Matrix (Fin d) (Fin d) R) := by rw [Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  exact sub_eq_zero.mp (smul_cancel hdM h1)

theorem map_smul_one (f : R →+* R) (c : R) :
    (c • (1 : Matrix (Fin d) (Fin d) R)).map f = f c • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_smul' (f : R →+* R) (c : R) (M : Matrix (Fin d) (Fin d) R) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_defect_eq (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R)
    (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R)
    (hlr : ∀ x : R, lr * x = 0 → x = 0) (hev : ∃ v : Rˣ, e = lr * v) (he₀v : ∃ v : Rˣ, e₀ = lr * v)
    (hφσ : ∀ x, φ (σ x) = σ (φ x)) (hφlr : φ lr = lr) (hσlr : σ lr = lr) (hσe₀ : σ e₀ = e₀)
    (hA₀σ : A₀.map σ = A₀)
    (hQQ' : Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R))
    (hBB' : B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hAA' : A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hQA : e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ))
    (hεB : e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ)) :
    e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) =
      A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  obtain ⟨v, hv⟩ := hev
  obtain ⟨v₀, hv₀⟩ := he₀v
  have he : ∀ x : R, e * x = 0 → x = 0 := by rw [hv]; exact nzd_unit hlr v
  have he₀ : ∀ x : R, e₀ * x = 0 → x = 0 := by rw [hv₀]; exact nzd_unit hlr v₀
  have hσe : ∀ x : R, σ e * x = 0 → x = 0 := by
    have : σ e = lr * ((Units.map (σ : R →* R) v : Rˣ) : R) := by
      rw [hv, map_mul, hσlr]; rfl
    rw [this]; exact nzd_unit hlr _
  have hL := nzd_pow hlr (2 * k)
  have hB'B : B' * B = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) :=
    mul_comm_of_nzd (nzd_pow he _) hBB'
  have hσBB' : B.map σ * B'.map σ = σ e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hBB', map_smul_one, map_pow]
  have hφQ'Q : Q'.map φ * Q.map φ = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, mul_comm_of_nzd hL hQQ', map_smul_one, map_pow, hφlr]

  have h1 : B' * (Q * A₀) = (e * e₀) ^ N • Q.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (Q * A₀)) = B' * (e ^ N • (Q * A₀)) := by rw [Matrix.mul_smul]
      _ = B' * (e₀ ^ N • (B * Q.map φ)) := by rw [hQA]
      _ = e₀ ^ N • (B' * (B * Q.map φ)) := by rw [Matrix.mul_smul]
      _ = e₀ ^ N • (e ^ (2 * N) • Q.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((e * e₀) ^ N • Q.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h2 : (e * e₀) ^ N • Q'.map φ = A₀' * (Q' * B) := by
    apply left_cancel hL hφQ'Q
    apply smul_cancel (nzd_pow (nzd_mul he he₀) N)
    have lhs : (e * e₀) ^ N • (Q.map φ * ((e * e₀) ^ N • Q'.map φ)) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [Matrix.mul_smul, ← Matrix.map_mul, hQQ', map_smul_one, map_pow, hφlr, smul_smul,
        smul_smul]
      congr 1; ring
    have rhs : (e * e₀) ^ N • (Q.map φ * (A₀' * (Q' * B))) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [← Matrix.smul_mul, ← h1, Matrix.mul_assoc, Matrix.mul_assoc, mul_left_of hAA',
        Matrix.mul_smul, Matrix.mul_smul, mul_left_of hQQ', Matrix.mul_smul, hB'B, smul_smul,
        smul_smul]
      congr 1; ring
    rw [lhs, rhs]

  have hcomm : (Q.map φ).map σ = (Q.map σ).map φ := by
    ext i j; simp [hφσ]
  have h3 : B'.map σ * (Q.map σ * A₀) = (σ e * e₀) ^ N • (Q.map σ).map φ := by
    have := congrArg (fun M => M.map σ) h1
    simp only [Matrix.map_mul, map_smul', map_pow, map_mul, hA₀σ, hσe₀, hcomm] at this
    exact this

  have h4 : B' * (ε * B.map σ) = (σ e * e) ^ N • ε.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (ε * B.map σ)) = B' * (e ^ N • (ε * B.map σ)) := by rw [Matrix.mul_smul]
      _ = B' * (σ e ^ N • (B * ε.map φ)) := by rw [hεB]
      _ = σ e ^ N • (B' * (B * ε.map φ)) := by rw [Matrix.mul_smul]
      _ = σ e ^ N • (e ^ (2 * N) • ε.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((σ e * e) ^ N • ε.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h5 : A₀ * (Q' * ε * Q.map σ).map φ * A₀' = e₀ ^ (2 * N) • (Q' * ε * Q.map σ) := by
    have hc := nzd_mul (nzd_mul (nzd_pow (nzd_mul he he₀) N) (nzd_pow (nzd_mul hσe he) N))
      (nzd_pow (nzd_mul hσe he₀) N)
    apply smul_cancel hc
    calc ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (A₀ * (Q' * ε * Q.map σ).map φ * A₀')
        = A₀ * (((e * e₀) ^ N • Q'.map φ) * (((σ e * e) ^ N • ε.map φ) *
            (((σ e * e₀) ^ N • (Q.map σ).map φ) * A₀'))) := by
          simp only [Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
          congr 1; ring
      _ = A₀ * ((A₀' * (Q' * B)) * ((B' * (ε * B.map σ)) * ((B'.map σ * (Q.map σ * A₀)) * A₀'))) := by
          rw [h2, h4, h3]
      _ = ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (e₀ ^ (2 * N) • (Q' * ε * Q.map σ)) := by
          simp only [Matrix.mul_assoc, mul_left_of hAA', mul_left_of hBB', mul_left_of hσBB', hAA',
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          congr 1; ring
  have hLφ : A₀ * (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' =
      e₀ ^ (2 * N) • (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) := by
    rw [map_smul_one, map_pow, hφlr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAA',
      smul_smul, smul_smul, mul_comm]
  have hsub : (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ =
      (Q' * ε * Q.map σ).map φ - (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h5, hLφ, smul_sub]

end GlobalTheory.FrobeniusDefect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPow
section
open scoped NNReal

namespace GlobalTheory

theorem phiEq_iterate (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [ExpChar R l] (u : R)
    (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ)
    (hD : ∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) (k : ℕ) :
    ∃ a : ℕ, a + h ≤ h * l ^ k ∧ ∃ e : κ → κ → R,
      ∀ j, u ^ a * D j = ∑ i, D i ^ (l ^ k) * e i j := by
  classical
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  induction k with
  | zero =>
    refine ⟨0, by simp, fun i j => if i = j then 1 else 0, fun j => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨a, ha, e, he⟩ := ih
    refine ⟨h + l * a, ?_, fun i' j => ∑ i, e i' i ^ l * c i j, fun j => ?_⟩
    · have h1 : l * (a + h) ≤ l * (h * l ^ k) := Nat.mul_le_mul_left _ ha
      have h2 : 2 * h ≤ l * h := Nat.mul_le_mul_right _ hl2
      calc h + l * a + h = 2 * h + l * a := by ring
        _ ≤ l * h + l * a := by omega
        _ = l * (a + h) := by ring
        _ ≤ l * (h * l ^ k) := h1
        _ = h * l ^ (k + 1) := by ring
    · calc u ^ (h + l * a) * D j = ∑ i, (u ^ a * D i) ^ l * c i j := by
            rw [pow_add, mul_comm (u ^ h) (u ^ (l * a)), mul_assoc, hD j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, ← pow_mul, mul_comm a l]; ring
        _ = ∑ i, (∑ i', D i' ^ (l ^ k) * e i' i) ^ l * c i j := by
            simp only [he]
        _ = ∑ i, ∑ i', D i' ^ (l ^ (k + 1)) * (e i' i ^ l * c i j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sum_pow_char, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [mul_pow, ← pow_mul, pow_succ]; ring
        _ = ∑ i', D i' ^ (l ^ (k + 1)) * ∑ i, e i' i ^ l * c i j := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]

theorem phiEq_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h hD hnil m j
  classical
  have hlp : l.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hchar : ringChar R = l := by
    rcases (Nat.dvd_prime hlp).1 (ringChar.dvd hl) with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  haveI : CharP R l := hchar ▸ ringChar.charP R
  haveI : ExpChar R l := ExpChar.prime hlp
  choose C hC using fun i => hnil i (h + 1)
  set Cm := ∑ i, C i with hCm
  obtain ⟨k, hk⟩ : ∃ k, m + Cm < l ^ k := ⟨m + Cm, Nat.lt_pow_self hlp.one_lt⟩
  obtain ⟨a, ha, e, he⟩ := phiEq_iterate l R u κ D c h hD k
  have hdiv : u ^ ((h + 1) * l ^ k) ∣ u ^ (Cm + a) * D j := by
    rw [pow_add, mul_assoc, he j, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    have hCi : C i ≤ Cm := Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ i)
    refine (hC i (l ^ k)).trans ?_
    have hsp : u ^ Cm = u ^ C i * u ^ (Cm - C i) := by rw [← pow_add, Nat.add_sub_cancel' hCi]
    rw [hsp]
    exact ⟨u ^ (Cm - C i), by ring⟩
  have hle : Cm + a + m ≤ (h + 1) * l ^ k := by
    have : h * l ^ k + l ^ k = (h + 1) * l ^ k := by ring
    omega
  obtain ⟨y, hy⟩ := hdiv
  have hsplit : (h + 1) * l ^ k = (Cm + a) + ((h + 1) * l ^ k - (Cm + a)) := by omega
  rw [hsplit, pow_add u (Cm + a), mul_assoc] at hy
  have hreg : u ^ (Cm + a) ∈ nonZeroDivisors R := pow_mem hu _
  have hDj := (mul_cancel_left_mem_nonZeroDivisors hreg).1 hy
  rw [hDj]
  refine Dvd.dvd.mul_right (pow_dvd_pow u ?_) _
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion
section
open scoped NNReal

namespace GlobalTheory

theorem WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteOfTrivialOnInfFiniteIndex
section
namespace GlobalTheory

theorem image_finite_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  intro G Q _ _ ρ J H hH hρ
  classical
  haveI := hH
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  apply (Set.finite_range (fun q : G ⧸ H =>
    if h : ∃ g ∈ J, (g : G ⧸ H) = q then ρ h.choose else 1)).subset
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨(g : G ⧸ H), ?_⟩
  have hex : ∃ g' ∈ J, (g' : G ⧸ H) = g := ⟨g, hg, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  obtain ⟨hJ, hq⟩ := hex.choose_spec
  have hmem : (hex.choose)⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
  have h1 := hρ _ (J.mul_mem (J.inv_mem hJ) hg) hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltraSumLe
section
namespace GlobalTheory.UltrametricSum

theorem ultra_sum_le {R : Type} [inst : CommRing R] (a : R → ℝ) (h0 : a (0 : R) = (0 : ℝ))
    (hadd : ∀ (x y : R), a (x + y) ≤ Max.max (a x) (a y)) {ι : Type} (s : Finset ι) (f : ι → R)
    (c : ℝ) (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, h0]; exact hc
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hadd _ _).trans (max_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GlobalTheory.UltrametricSum
end

