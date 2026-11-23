module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem rFin_const {a : ℕ} (c : ℂ) : RFin (fun _ : GL (Fin a) ℂ => c) := by
  refine ⟨continuous_const, Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, fun y => ?_⟩
  exact Submodule.mem_span_singleton.2 ⟨c, by funext n; simp⟩

private theorem rFin_add {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h + q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.add cq, A ⊔ B, inferInstance, fun y => ?_⟩
  have h := Submodule.add_mem_sup (mA y) (mB y)
  exact h

private theorem rFin_mul {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h * q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.mul cq, A * B, ?_, fun y => ?_⟩
  · have h1 : A.FG := (Submodule.fg_iff_finiteDimensional A).2 fA
    have h2 : B.FG := (Submodule.fg_iff_finiteDimensional B).2 fB
    exact (Submodule.fg_iff_finiteDimensional _).1 (h1.mul h2)
  · have h := Submodule.mul_mem_mul (mA y) (mB y)
    exact h

private theorem rFin_entry {a : ℕ} (i j : Fin a) :
    RFin (fun h : GL (Fin a) ℂ => (h : Matrix (Fin a) (Fin a) ℂ) i j) := by
  refine ⟨Units.continuous_val.matrix_elem i j,
    Submodule.span ℂ (Set.range fun r : Fin a => fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), fun y => ?_⟩
  have h : (fun n : GL (Fin a) ℂ => ((n * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ r, (y : Matrix (Fin a) (Fin a) ℂ) r j • fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r := by
    funext n
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private theorem rFin_of_rep {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : GL (Fin a) ℂ →* (V →ₗ[ℂ] V)) (l : V →ₗ[ℂ] ℂ) (v : V) (X : GL (Fin a) ℂ)
    (hc : Continuous fun h : GL (Fin a) ℂ => l (ρ h v)) : RFin fun n => l (ρ (X * n) v) := by
  refine ⟨hc.comp (continuous_const.mul continuous_id),
    LinearMap.range (LinearMap.pi fun n : GL (Fin a) ℂ => l ∘ₗ ρ (X * n)), inferInstance,
    fun y => ⟨ρ y v, ?_⟩⟩
  funext n
  change l (ρ (X * n) (ρ y v)) = l (ρ (X * (n * y)) v)
  rw [← mul_assoc, map_mul ρ (X * n) y]
  rfl

private theorem rFin_delta {a : ℕ} (ν : DomWeight a) (X : GL (Fin a) ℂ) : RFin fun n => delta ν (X * n) := by
  haveI : FiniteDimensional ℂ (nablaSq ℂ a ν) := inferInstance
  exact rFin_of_rep (sqRep ℂ a ν) (ev1 ν) (top ν) X (GlobalTheory.BCT.TrKer.continuous_coef_sqRep a ν (top ν) (ev1 ν))

theorem UpperTheory.Gal.Wt.rFinEx_of :
    UpperTheory.Gal.Wt.RFinEx := by
  intro a
  refine ⟨rFin_delta, fun P => ?_⟩
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : pev (MvPolynomial.C c : MvPolynomial (Fin a × Fin a) ℂ) = fun _ => c := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_const c
  | add p q hp hq =>
    have h : pev (p + q) = fun g => pev p g + pev q g := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_add hp hq
  | mul_X p n hp =>
    have h : pev (p * MvPolynomial.X n) = fun g => pev p g * (g : Matrix (Fin a) (Fin a) ℂ) n.1 n.2 := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_mul hp (rFin_entry n.1 n.2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem mvEval_aeval_X_sub_C_eq_eval_sub {k : Type} [Field k] {σ : Type} (p : Polynomial k) (i : σ) (c : k)
    (z : σ → k) :
    MvPolynomial.eval z (Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C c) p) =
      Polynomial.eval (z i - c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

private theorem norm_prod_sub_one_le_of_norm_sub_one_le {k : Type} [NormedField k] [IsUltrametricDist k] {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f : ι → k) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (h : ∀ j ∈ s, ‖f j - 1‖ ≤ c) : ‖∏ j ∈ s, f j - 1‖ ≤ c := by
  induction s using Finset.induction_on with
  | empty => simpa using hc0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hx : ‖f j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (f j - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (h1.trans hc) le_rfl)
    have e : f j * ∏ l ∈ s, f l - 1 = f j * (∏ l ∈ s, f l - 1) + (f j - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rw [norm_mul]
    calc ‖f j‖ * ‖∏ l ∈ s, f l - 1‖ ≤ 1 * c := mul_le_mul hx h2 (norm_nonneg _) zero_le_one
      _ = c := one_mul c

private theorem norm_one_sub_le_one_of_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {x : k}
    (h : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_one]
  · rw [norm_neg]
    exact h

theorem UpperTheory.Gal.Wt.sepPoly_of :
    UpperTheory.Gal.Wt.Kapl → UpperTheory.Gal.Wt.SepPoly := by
  intro hK k _ _ σ _ Z₁ Z₂ h₁ h₂ hd ε hε
  classical
  obtain ⟨D, hD, hDd⟩ := hd.exists_thickenings h₁ h₂.isClosed
  have he0 : 0 < min ε 1 := lt_min hε one_pos
  have he1 : min ε 1 ≤ 1 := min_le_right _ _
  have heε : min ε 1 ≤ ε := min_le_left _ _
  obtain ⟨T, hTsub, hTfin, hcov⟩ := h₁.finite_cover_balls (mul_pos hD he0)
  obtain ⟨Y, hY, hmemY⟩ : ∃ Y : Set k, IsCompact Y ∧
      ∀ i, ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, z i - a i ∈ Y := by
    refine ⟨⋃ i : σ, ⋃ a ∈ hTfin.toFinset, (fun z : σ → k => z i - a i) '' (Z₁ ∪ Z₂), ?_, ?_⟩
    · exact isCompact_iUnion fun i => hTfin.toFinset.isCompact_biUnion fun a _ =>
        (h₁.union h₂).image (by fun_prop)
    · intro i a ha z hz
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨a, ha, z, hz, rfl⟩⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := hK k Y hY D (min ε 1) hD he0 he1
  obtain ⟨q, hq⟩ : ∃ q : (σ → k) → MvPolynomial σ k,
      ∀ a z, MvPolynomial.eval z (q a) = ∏ i, Polynomial.eval (z i - a i) p :=
    ⟨fun a => ∏ i, Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C (a i)) p,
      fun a z => by simp only [map_prod, mvEval_aeval_X_sub_C_eq_eval_sub]⟩
  have hqle : ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, ‖MvPolynomial.eval z (q a)‖ ≤ 1 := by
    intro a ha z hz
    rw [hq, norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hp1 _ (hmemY i a ha z hz))
  refine ⟨1 - ∏ a ∈ hTfin.toFinset, (1 - q a), ?_, ?_⟩
  · intro z hz
    obtain ⟨a0, ha0T, hza⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have ha0 : a0 ∈ hTfin.toFinset := hTfin.mem_toFinset.2 ha0T
    have hnear : ‖MvPolynomial.eval z (q a0) - 1‖ ≤ min ε 1 := by
      rw [hq]
      apply norm_prod_sub_one_le_of_norm_sub_one_le _ _ he0.le he1
      intro i _
      apply hp3
      have := norm_le_pi_norm (z - a0) i
      rw [Metric.mem_ball, dist_eq_norm] at hza
      simp only [Pi.sub_apply] at this
      linarith
    simp only [map_sub, map_one, map_prod]
    rw [show (1 : k) - ∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) - 1 =
        -∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) by ring, norm_neg, norm_prod,
      ← Finset.mul_prod_erase _ _ ha0]
    have hrest : ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖ ≤ 1 := by
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro a ha
      exact norm_one_sub_le_one_of_norm_le_one (hqle a (Finset.mem_of_mem_erase ha) z (Or.inl hz))
    have h0 : ‖1 - MvPolynomial.eval z (q a0)‖ ≤ min ε 1 := by
      rw [norm_sub_rev]
      exact hnear
    calc ‖1 - MvPolynomial.eval z (q a0)‖ *
          ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖
        ≤ min ε 1 * 1 := mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
      _ ≤ ε := by linarith
  · intro z hz
    have hfar : ∀ a ∈ hTfin.toFinset, ‖MvPolynomial.eval z (q a)‖ ≤ min ε 1 := by
      intro a ha
      have hdist : D ≤ ‖z - a‖ := by
        by_contra hlt
        push_neg at hlt
        apply Set.disjoint_left.1 hDd
          (Metric.self_subset_thickening hD _ (hTsub (hTfin.mem_toFinset.1 ha)))
        exact Metric.mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm, norm_sub_rev]; exact hlt⟩
      obtain ⟨i, hi⟩ : ∃ i, D ≤ ‖z i - a i‖ := by
        by_contra hno
        push_neg at hno
        have := (pi_norm_lt_iff (x := z - a) hD).2 (fun i => by simpa using hno i)
        linarith
      rw [hq, norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      have h0 := hp2 _ (hmemY i a ha z (Or.inr hz)) hi
      have hrest : ∏ j ∈ Finset.univ.erase i, ‖Polynomial.eval (z j - a j) p‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hp1 _ (hmemY j a ha z (Or.inr hz)))
      calc _ ≤ min ε 1 * 1 :=
            mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
        _ = min ε 1 := mul_one _
    simp only [map_sub, map_one, map_prod]
    have := norm_prod_sub_one_le_of_norm_sub_one_le hTfin.toFinset (fun a => 1 - MvPolynomial.eval z (q a)) he0.le he1
      (fun a ha => by
        rw [show (1 : k) - MvPolynomial.eval z (q a) - 1 = -MvPolynomial.eval z (q a) by ring,
          norm_neg]
        exact hfar a ha)
    rw [norm_sub_rev]
    linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

set_option maxHeartbeats 400000 in
private theorem coeff_diag {a : ℕ} (t : Fin a → ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) (m : Fin a × Fin a →₀ ℕ) :
    AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (Matrix.diagonal t) f) m = (∏ v : Fin a × Fin a, t v.1 ^ m v) * AddMonoidAlgebra.coeff f m := by
  have hg : (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2))
      = fun v => MvPolynomial.C (t v.1) * MvPolynomial.X v := by
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne t (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show AddMonoidAlgebra.coeff (MvPolynomial.aeval
      (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) f) m = _
  rw [hg]
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [mul_one, mul_comm]
      congr 1
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro v _ hv
      simp only [Finsupp.mem_support_iff, not_not] at hv
      rw [hv, pow_zero]
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem UpperTheory.Gal.Wt.sqExp_h : ExpBasic → EvLem → Dom → SqExp := by
  intro hE hEv hDom a k κ w L
  obtain ⟨_, _, hle, hmon, _, _⟩ := hE
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (Finset.univ.filter fun i : Fin a => (i : ℕ) < k).card := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin a × Fin a →₀ ℕ) → ℕ,
      e = fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), Formalism.GradedWeylDivisibility.rowDeg m i := ⟨_, rfl⟩
  have hdet : ∀ z : Circle, detPow ℂ a (tor a k z) κ.detShift = (z : ℂ) ^ ((D : ℤ) * κ.detShift) := by
    intro z
    simp only [detPow]
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, tor_coe, Matrix.det_diagonal,
      ← Finset.prod_filter, Finset.prod_const, zpow_mul, zpow_natCast, hD]
  have hprod : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      (∏ v : Fin a × Fin a, (if ((v.1 : Fin a) : ℕ) < k then (z : ℂ) else 1) ^ m v) = (z : ℂ) ^ e m := by
    intro z m
    have hin : ∀ i : Fin a, (∏ s : Fin a, (if (i : ℕ) < k then (z : ℂ) else 1) ^ m (i, s))
        = if (i : ℕ) < k then (z : ℂ) ^ Formalism.GradedWeylDivisibility.rowDeg m i else 1 := by
      intro i
      split_ifs
      · rw [Finset.prod_pow_eq_pow_sum]
        rfl
      · simp
    rw [Fintype.prod_prod_type]
    dsimp only
    simp only [hin]
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, he]
  have hcoeff : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      AddMonoidAlgebra.coeff ((sqRep ℂ a κ (tor a k z) w : nablaSq ℂ a κ) : MvPolynomial (Fin a × Fin a) ℂ) m
        = AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) m
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e m : ℤ)) := by
    intro z m
    show AddMonoidAlgebra.coeff (sqAct ℂ a κ (tor a k z) (w : MvPolynomial (Fin a × Fin a) ℂ)) m = _
    rw [sqAct, MvPolynomial.coeff_smul, hdet, tor_coe, Matrix.diagonal_transpose, coeff_diag]
    beta_reduce
    rw [hprod, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero z), zpow_natCast]
    ring
  let ev : (Fin a × Fin a →₀ ℕ) → nablaSq ℂ a κ →ₗ[ℂ] ℂ :=
    fun x => (MvPolynomial.lcoeff ℂ x).comp (nablaSq ℂ a κ).subtype
  have hsep : ∀ p : nablaSq ℂ a κ, (∀ x, ev x p = 0) → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext x
    simpa [ev] using hp x
  have hterm : ∀ T : Submodule ℂ (Circle → ℂ),
      (∀ x, AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x ≠ 0 →
        (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) ∈ T) →
      (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ T := by
    intro T hT
    refine hEv (nablaSq ℂ a κ) (Fin a × Fin a →₀ ℕ) Circle ev hsep T (fun z => sqRep ℂ a κ (tor a k z) w) ?_ L
    intro x
    have hfun : (fun z => ev x (sqRep ℂ a κ (tor a k z) w))
        = fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ)) := funext fun z => hcoeff z x
    rw [hfun]
    by_cases hx : AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x = 0
    · have h0 : (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) = 0 := by
        funext z
        simp [hx]
      rw [h0]
      exact T.zero_mem
    · exact hT x hx
  have hds : ∀ i : Fin a, κ.detShift ≤ κ.w i := by
    intro i
    simp only [DomWeight.detShift, dif_pos (Fin.pos i)]
    exact κ.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  have hnat : ∀ i : Fin a, ((κ.natW i : ℕ) : ℤ) = κ.w i - κ.detShift :=
    fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hds i))
  have hDa : D ≤ a := by
    rw [hD]
    exact (Finset.card_filter_le _ _).trans (Finset.card_fin a).le
  refine ⟨hterm _ fun x hx => ?_, hterm _ fun x _ => ?_⟩
  · have hxs : x ∈ (w : MvPolynomial (Fin a × Fin a) ℂ).support := MvPolynomial.mem_support_iff.mpr hx
    have hbound := hDom a κ _ w.2 x hxs k
    have hup : (D : ℤ) * κ.detShift + (e x : ℤ) ≤ psum κ k := by
      have h1 : (e x : ℤ) ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) := by
        rw [he]
        exact_mod_cast hbound
      have h2 : (D : ℤ) * κ.detShift
          + ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) = psum κ k := by
        rw [Nat.cast_sum]
        simp only [hnat]
        rw [Finset.sum_sub_distrib, hD, psum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      linarith
    exact (hle _ _ hup).1 (hmon _ _).1
  · have hlow : -((a * κ.detShift.natAbs : ℕ) : ℤ) ≤ (D : ℤ) * κ.detShift + (e x : ℤ) := by
      have hD0 : (0 : ℤ) ≤ D := Int.natCast_nonneg D
      have hDa' : (D : ℤ) ≤ a := by exact_mod_cast hDa
      have he0 : (0 : ℤ) ≤ (e x : ℤ) := Int.natCast_nonneg _
      have habs : 0 ≤ κ.detShift + |κ.detShift| := by linarith [neg_abs_le κ.detShift]
      push_cast
      nlinarith [mul_nonneg hD0 habs, mul_nonneg (sub_nonneg.mpr hDa') (abs_nonneg κ.detShift)]
    exact (hle _ _ hlow).2 (hmon _ _).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

open UpperTheory.Gal.Gen UpperTheory.Gal.Int.Cong in
theorem top_of : FamEx → FamProj → FamWt → UpperTheory.Gal.Int.Cong.WtLacEx := by
  intro hEx hPr hWt E _ _ _ l _ ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η ht htv hact τ₀ hτ₀ U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam _ U (inf_le_left.trans hK.fin) hU w₀
  obtain rfl : lam = W.at := (funext hW).symm
  obtain ⟨X, b, hbd, hdef, hne⟩ := Loc.frame denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds ι W t fun j => Or.inr (ht j)
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W (K ⊓ Kv.comap (cLoc v')) := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨d, M, hM, hB⟩ := hEx E l ι a ha w₀ hw₀ hs₀ v' hsv hap K hK hKv Kv hKvo W f₁ hf₁K τ₀ hτ₀ X b hbd ε hε
  let N : ℕ := (a + 1) * (2 * (2 * d) + a) + 1
  let ν : DomWeight a := ⟨fun k => (N : ℤ) * mu0 a k, fun _ _ h => mul_le_mul_of_nonneg_left (lacunaryBaseWeight_antitone a h) (Int.natCast_nonneg N)⟩
  obtain ⟨B, hFam, hnear⟩ := hB ν
  obtain ⟨s₀, F, hF, hsum⟩ := hPr E a τ₀ W K ν d B hFam
  let I := s₀.filter fun V => ∃ y₁ y₂ v, F V y₁ y₂ v ≠ 0
  let Ft : Submodule ℂ (UA E a → ℂ) → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V =>
    LinearMap.pi fun g => (LinearMap.proj g) ∘ₗ F V (M g) (M g)
  have hFt : ∀ V v g, Ft V v g = F V (M g) (M g) v g := fun _ _ _ => rfl
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V => -Ft V.1
  have hop : ∀ j (φ : UA E a → ℂ) g, opOf (RU E a) (t j) φ g = ∑ h ∈ (t j).support, t j h * φ (g * h) := fun j φ g => by
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
  have heig : ∀ (V : ↥I) j, T j (vv V) = η V.1 j • vv V := by
    rintro ⟨V, hV⟩ j
    obtain ⟨h1, h2, h3⟩ := hF V (Finset.mem_filter.1 hV).1
    have h : T j (Ft V) = η V j • Ft V := by
      apply LinearMap.ext; intro v
      funext g
      have e := congrFun (hact V h1 _ (h3 (M g) (M g) v) (fun x hx => h2.fix x hx.1 _ _ _) j) g
      rw [hT, hop, LinearMap.smul_apply, Pi.smul_apply, hFt]
      rw [hop, Pi.smul_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hFt, hM g h (ht j h hh).1 ((htv j h hh).2 v' (not_apart_self v'))]
    show T j (-Ft V) = η V j • -Ft V
    rw [map_neg, h, smul_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ V, vv V))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ V, vv V) = f₁.1 (b x.1 x.2) x.1 - B (M x.1) (M x.1) (b x.1 x.2) x.1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hev, sub_eq_add_neg, ← hsum, Finset.sum_apply, ← Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_coe_sort I (fun V => ev x (-Ft V))]
      refine (Finset.sum_filter_of_ne fun V _ hV => ?_).trans (Finset.sum_congr rfl fun V _ => rfl)
      by_contra h
      push_neg at h
      refine hV ?_
      rw [map_neg, hev, hFt, h, Pi.zero_apply, neg_zero]
    rw [h1]
    exact hnear _ _
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv (fun V => η V.1) heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨V, hV⟩, rfl⟩ := hs z hz'
  obtain ⟨hV1, hV2⟩ := Finset.mem_filter.1 hV
  obtain ⟨h1, h2, h3⟩ := hF V hV1
  obtain ⟨mu, g1, g2, g3⟩ := hWt E a τ₀ W K ν d (F V) h2 V h1 h3 hV2
  refine ⟨V, mu, fun τ hτ => ?_, gapJ_of_near (mu τ₀) N (2 * d) g3 (Nat.lt_succ_self _), g1, rfl⟩
  have e : InfinitePlace.mk τ = InfinitePlace.mk τ₀ := by
    by_contra h
    exact hτ (g2 τ h)
  rcases InfinitePlace.mk_eq_iff.1 e with rfl | rfl
  · exact Or.inl hτ₀
  · refine Or.inr fun x hx => ?_
    have := hτ₀ x hx
    rwa [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj] at this

end UpperTheory.Gal.Wt

end
end

