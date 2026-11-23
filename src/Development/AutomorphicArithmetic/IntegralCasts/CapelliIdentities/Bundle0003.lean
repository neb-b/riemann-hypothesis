module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AgreeOfAdjoin
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.Qk58.agree_of_adjoin :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (φ ψ : E →+* ℂ) {a b : E},
    (φ : E → ℂ) a = (ψ : E → ℂ) a → b ∈ ℚ⟮a⟯ → (φ : E → ℂ) b = (ψ : E → ℂ) b := by
  intro E _ _ φ ψ a b ha hb
  induction hb using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ha
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraicPointIntegral
section
open Polynomial

private theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (p : O[X])
    (hp : ∃ i, p.coeff i ∉ IsLocalRing.maximalIdeal O) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    obtain ⟨i, hi⟩ := hp
    intro h
    apply hi
    have := congrArg (PowerSeries.coeff i) h
    rwa [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero,
      IsLocalRing.residue_eq_zero_iff] at this
  obtain ⟨g, h, hg, hh, e⟩ := PowerSeries.exists_isWeierstrassFactorization h0
  have hI : IsLocalRing.maximalIdeal O ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hd := hg.isWeierstrassDivisorAt hI
  have hn : (((g : PowerSeries O).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree := by
    rw [← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1
      (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]
    simp
  have hdeg : g.degree = g.natDegree := Polynomial.degree_eq_natDegree hg.monic.ne_zero
  have e2 := Polynomial.modByMonic_add_div p g
  have key := hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O))
    (r := 0) (r' := p %ₘ g)
    (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic)
    (by
      rw [← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add,
        add_comm, e2])
  refine ⟨g, p /ₘ g, hg.monic, ?_, ?_⟩
  · have := PowerSeries.isUnit_iff_constantCoeff.1 hh
    rw [key.1] at this
    simpa using this
  · rw [← key.2, zero_add] at e2
    exact e2.symm

theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type} [inst_4 : CommRing R]
    [inst_5 : Algebra O R] [inst_6 : IsLocalRing R] {K : Type} [inst_7 : Field K] [inst_8 : Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R, IsIntegral O ((f : R → K) a) := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f a ha
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid O) := inferInstance
  have h1 : aeval (f a) p.primPart = 0 := aeval_primPart_eq_zero hp0 hp
  have h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O := by
    by_contra hc
    push Not at hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    apply hϖ.not_isUnit
    apply isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := hc i
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨g, q, hg, hq, e⟩ := UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2
  have h3 : IsUnit (aeval a q) := by
    by_contra hu
    have hm : aeval a q ∈ IsLocalRing.maximalIdeal R := hu
    have e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add q]
      simp
    rw [e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)] at hm
    exact hm (hq.map _)
  have h4 : aeval (f a) q ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (h3.map f).ne_zero
  rw [e, map_mul] at h1
  exact ⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlternatingSumZero
section
theorem UpperTheory.Reformulated.B.AlternatingSumZero.alt_sum_zero.{u_1} :
    ∀ {A : Type u_1} [inst : AddCommGroup A] {n : ℕ}
      (G : ({ len := n : SimplexCategory } ⟶ { len := n + (2 : ℕ) : SimplexCategory }) → A),
      ∑ i : Fin (n + (3 : ℕ)),
          ∑ j : Fin (n + (2 : ℕ)),
            ((-1 : ℤ) ^ (↑i : ℕ) * (-1 : ℤ) ^ (↑j : ℕ)) •
              G (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ j) (SimplexCategory.δ i)) =
        (0 : A) := by
  intro A _ n G
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 3) × Fin (n + 2) => (p.1 : ℕ) ≤ (p.2 : ℕ)), add_eq_zero_iff_eq_neg,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun p hp => (p.2.succ, p.1.castLT
      (lt_of_le_of_lt (Finset.mem_filter.mp hp).2 p.2.isLt))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ h
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    have hi := i.isLt
    simp only [not_le] at h
    refine ⟨(j.castSucc, ⟨i.val - 1, by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
      omega
    · simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT, Fin.val_castSucc,
        and_true]
      omega
  · rintro ⟨i, j⟩ hp
    have h : (i : ℕ) ≤ (j : ℕ) := (Finset.mem_filter.mp hp).2
    have hi : (i : ℕ) < n + 2 := lt_of_le_of_lt h j.isLt
    have key := SimplexCategory.δ_comp_δ (i := i.castLT hi) (j := j) h
    rw [Fin.castSucc_castLT] at key
    dsimp only
    rw [key, ← neg_smul]
    congr 1
    simp only [Fin.val_succ, Fin.val_castLT]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation
section
noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, hb]
  · simp

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro rfl <;> simp

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g) = g := by
  intro m R _ g
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl]
  rw [mul_assoc, mul_assoc, mul_assoc, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, mul_one, ← mul_assoc,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g * UpperTheory.Reformulated.B.AntidiagonalConjugation.theta h := by
  intro m R _ g h
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m), UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left *
          ((UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h * r g * (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h)⁻¹).left = _
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
    MulAut.one_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Artin
section
theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing
section
noncomputable def UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing :
    (K : Type) → [inst : NormedField K] → [IsUltrametricDist K] → Subring K :=
  fun K _ _ =>
    { carrier := {x : K | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : K)‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : K)‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha' }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup
section
noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BiHomSum
section
noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff F β) n ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d

theorem UpperTheory.Reformulated.B.Qf22.biHom_sum.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlkB
section
noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}

noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ

theorem UpperTheory.Reformulated.B.Yha8.main :
    ∀ {n : ℕ} (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ),
      (∀ (a b : Fin n), Q a b ≠ (0 : ℂ) → b ∈ UpperTheory.Reformulated.B.Yha8.blkA j) →
        (∀ (a b : Fin n), S a b ≠ (0 : ℂ) → a ∈ UpperTheory.Reformulated.B.Yha8.blkB j) → Q * S = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro n j Q S hQ hS
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hq : Q a b = 0
  · simp [hq]
  by_cases hs : S b c = 0
  · simp [hs]
  exfalso
  have h1 := hQ a b hq
  have h2 := hS b c hs
  unfold UpperTheory.Reformulated.B.Yha8.blkB at h2
  rw [Finset.mem_compl] at h2
  exact h2 h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonMajorizingLattice
section
theorem UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [NumberField K] (t : Finset K),
    ∃ (d : ℤ), d ≠ (0 : ℤ) ∧ ∀ a ∈ t, IsIntegral ℤ ((↑d : K) * a) := by
  intro K _ _ t
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ t
  exact ⟨d, hd, fun a ha => by simpa [zsmul_eq_mul] using h a ha⟩
end

