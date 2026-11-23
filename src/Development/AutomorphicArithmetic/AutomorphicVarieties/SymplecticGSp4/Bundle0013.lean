module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ShaCoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (ha0 : 0 ≤ a) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ha1
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy n _ (Ideal.Quotient.eq.1 hg)) hn

theorem UpperTheory.V.GradeZeroInterpolatingElement.eptInt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → Continuous r ∧ (∀ g i j, ‖r g i j - D.r0E g i j‖ < 1) ∧ ∃ c' : Coef l, c.O ≤ c'.O ∧ (∀ g i j, r g i j ∈ c'.O) ∧ ∀ i, ∃ (s : Finset (G ℚ Ω)) (a : G ℚ Ω → PadicAlgCl l), (∀ g, a g ∈ c'.O) ∧ Matrix.single i i (1 : PadicAlgCl l) = ∑ g ∈ s, a g • r g := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, ha0, hy⟩ := (coPt c R).1 y
  refine ⟨?_, fun g i j => ?_, c', hc', fun g i j => hy' _, fun i => ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact cont_of_adic (maximalIdeal R) (y : R →+* PadicAlgCl l) a ha1 ha0 hy _ (ρ.cont i j)
  · have hm : ρ.hom g i j - algebraMap c.O R (D.r0 g i j) ∈ maximalIdeal R ^ 1 := by
      rw [pow_one, ← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ρ.red, sub_eq_zero]
      rfl
    have h := hy 1 _ hm
    rw [map_sub, AlgHom.commutes, pow_one] at h
    exact lt_of_le_of_lt h ha1
  · have h := eii D hD R ρ hρ.mult hρ.nrm i
    obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
    refine ⟨b.support, fun g => y (b g), fun g => hy' _, ?_⟩
    ext p q
    have h2 := congrArg y (congrFun (congrFun hb p) q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, Matrix.sum_apply, map_sum] at h2
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at h2 ⊢
    have h3 : y (Matrix.single i i (1 : R) p q) = Matrix.single i i (1 : PadicAlgCl l) p q := by
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [← h3, ← h2]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLocalFirstOrderLifts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Alg

variable {B : Type} [CommRing B]

private theorem adj_mul (X Y : M4 B) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] <;> ring

private theorem adj_one : adj (1 : M4 B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem gsp_conj {ν : B} {h : (M4 B)ˣ} (h1 : adj (h : M4 B) = (h⁻¹ : (M4 B)ˣ)) {X : M4 B} (hX : IsGSp ν X) :
    IsGSp ν (h * X * (h⁻¹ : (M4 B)ˣ)) := by
  have hinv : adj ((h⁻¹ : (M4 B)ˣ) : M4 B) = h := by
    have e1 : adj ((h⁻¹ : (M4 B)ˣ) : M4 B) * adj (h : M4 B) = 1 := by
      rw [← adj_mul, Units.mul_inv, adj_one]
    rw [h1] at e1
    calc adj ((h⁻¹ : (M4 B)ˣ) : M4 B)
        = adj ((h⁻¹ : (M4 B)ˣ) : M4 B) * (((h⁻¹ : (M4 B)ˣ) : M4 B) * h) := by rw [Units.inv_mul, mul_one]
      _ = h := by rw [← mul_assoc, e1, one_mul]
  unfold IsGSp at hX ⊢
  rw [adj_mul, adj_mul, hinv, h1]
  rw [show (h : M4 B) * (adj X * ((h⁻¹ : (M4 B)ˣ) : M4 B)) * (h * X * ((h⁻¹ : (M4 B)ˣ) : M4 B)) =
      h * (adj X * X) * ((h⁻¹ : (M4 B)ˣ) : M4 B) by simp only [mul_assoc, Units.inv_mul_cancel_left]]
  rw [hX, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]

private def cj {H : Type} [Group H] (h : (M4 B)ˣ) (r : H →* M4 B) : H →* M4 B where
  toFun g := h * r g * (h⁻¹ : (M4 B)ˣ)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left]

private theorem cj_apply {H : Type} [Group H] (h : (M4 B)ˣ) (r : H →* M4 B) (g : H) :
    cj h r g = h * r g * (h⁻¹ : (M4 B)ˣ) := rfl

private def cjA (h : (M4 B)ˣ) : M4 B →ₐ[B] M4 B where
  toFun X := h * X * (h⁻¹ : (M4 B)ˣ)
  map_one' := by simp
  map_mul' a b := by simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by rw [mul_add, add_mul]
  commutes' a := by simp [Algebra.algebraMap_eq_smul_one]

private theorem prj_cjA_eq_cjA_prj (h : (M4 B)ˣ) (c : Fin 4 → B) (X : M4 B) (i : Fin 4) :
    prj c (cjA h X) i = cjA h (prj c X i) := by
  simp only [prj, Polynomial.aeval_algHom_apply]

private theorem ord_cj {H : Type} [Group H] (h : (M4 B)ˣ) {I : Subgroup H} {ps : Fin 4 → H → B} {s₀ : H}
    {r : H →* M4 B} (hr : Ord I ps s₀ r) : Ord I ps s₀ (cj h r) := by
  have hcj : ∀ g, cj h r g = cjA h (r g) := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hcj]
    show ((h : M4 B) * r s₀ * ((h⁻¹ : (M4 B)ˣ) : M4 B)).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    exact hr.charpoly
  · intro g i j hij
    simp only [hcj, prj_cjA_eq_cjA_prj, ← map_mul, hr.stable g i j hij, map_zero]
  · intro s hs i
    have e : cjA h (r s) - ps i s • 1 = cjA h (r s - ps i s • 1) := by
      rw [map_sub, map_smul, map_one]
    simp only [hcj, prj_cjA_eq_cjA_prj, e, ← map_mul, hr.inert s hs i, map_zero]

private def cjL {O : Type} [CommRing O] [IsLocalRing O] [Algebra O B] [IsCO O B] {H : Type} [Group H] [TopologicalSpace H]
    {rb : H →* M4 (ResidueField O)} (h : (M4 B)ˣ) (h1 : (h : M4 B).map (res O B) = 1)
    (h2 : ((h⁻¹ : (M4 B)ˣ) : M4 B).map (res O B) = 1) (r : Lift O rb B) : Lift O rb B where
  hom := cj h r.hom
  cont a b N := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have : ∀ᶠ y in nhds x, ∀ i j, Ideal.Quotient.mk (maximalIdeal B ^ N) (r.hom y i j) =
        Ideal.Quotient.mk (maximalIdeal B ^ N) (r.hom x i j) :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (r.cont i j N).eventually_eq x
    filter_upwards [this] with y hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cj_apply, Matrix.mul_apply, map_sum, map_mul, hy]
  red g a b := by
    have : (cj h r.hom g).map (res O B) = (r.hom g).map (res O B) := by
      rw [cj_apply, Matrix.map_mul, Matrix.map_mul, h1, h2, one_mul, mul_one]
    exact (congrFun (congrFun this a) b).trans (r.red g a b)

end Alg

section Dual

variable {O : Type} [CommRing O]

private def dU (Y : M4 O) : (M4 (DualNumber O))ˣ :=
  have h : Y.map (TrivSqZeroExt.inr : O → DualNumber O) * Y.map (TrivSqZeroExt.inr : O → DualNumber O) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.map_apply, TrivSqZeroExt.inr_mul_inr, Finset.sum_const_zero, Matrix.zero_apply]
  ⟨1 + Y.map TrivSqZeroExt.inr, 1 - Y.map TrivSqZeroExt.inr, by rw [mul_sub, add_mul, add_mul, h]; simp,
    by rw [mul_add, sub_mul, sub_mul, h]; simp⟩

private theorem dU_val (Y : M4 O) : (dU Y : M4 (DualNumber O)) = 1 + Y.map TrivSqZeroExt.inr := rfl

private theorem dU_inv (Y : M4 O) :
    (((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) = 1 - Y.map TrivSqZeroExt.inr := rfl

private theorem dU_adj {Y : M4 O} (hY : Y ∈ sp4 O) :
    adj (dU Y : M4 (DualNumber O)) = ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) := by
  have hY' : adj Y = -Y := hY
  rw [dU_val, dU_inv]
  ext i j
  · rw [adj_apply]
    fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, Matrix.one_apply]
  · have hij := congrFun (congrFun hY' i) j
    rw [adj_apply] at hij
    rw [adj_apply]
    simp [Matrix.one_apply]
    rw [zsmul_eq_mul, Int.cast_mul, Matrix.neg_apply] at hij
    have e1 : TrivSqZeroExt.snd (if j = i then ((sgn i : DualNumber O) * (sgn j : DualNumber O)) else 0) = 0 := by
      split_ifs <;> simp
    have e2 : (if i = j then (1 : DualNumber O) else 0).snd = 0 := by
      split_ifs <;> simp
    rw [e1, e2, zero_add, zero_sub, mul_comm, hij]

private theorem map_fst_mul_dualNumber_matrix (A B : M4 (DualNumber O)) :
    (A * B).map TrivSqZeroExt.fst = A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem map_snd_mul_dualNumber_matrix (A B : M4 (DualNumber O)) :
    (A * B).map TrivSqZeroExt.snd =
      A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.snd + A.map TrivSqZeroExt.snd * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib, mul_comm]

private theorem dU_conj (Y X : M4 O) (X' : M4 (DualNumber O)) (hX : ∀ a b, X' a b = TrivSqZeroExt.inl (X a b))
    (a b : Fin 4) :
    ((dU Y * X' * ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) a b).fst = X a b ∧
      ((dU Y * X' * ((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)) a b).snd = (Y * X - X * Y) a b := by
  have hX' : X' = X.map TrivSqZeroExt.inl := Matrix.ext fun a b => hX a b
  subst hX'
  rw [dU_val, dU_inv]
  have p1 : (1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.fst = 1 := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have p2 : (1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.snd = Y := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have q1 : (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.fst = 1 := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have q2 : (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map TrivSqZeroExt.snd = -Y := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  have x1 : (X.map (TrivSqZeroExt.inl : O → DualNumber O)).map TrivSqZeroExt.fst = X := by
    ext a b
    simp
  have x2 : (X.map (TrivSqZeroExt.inl : O → DualNumber O)).map TrivSqZeroExt.snd = 0 := by
    ext a b
    simp
  have F : ((1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)) * X.map TrivSqZeroExt.inl *
      (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O))).map TrivSqZeroExt.fst = X := by
    rw [map_fst_mul_dualNumber_matrix, map_fst_mul_dualNumber_matrix, p1, x1, q1, one_mul, mul_one]
  have S : ((1 + Y.map (TrivSqZeroExt.inr : O → DualNumber O)) * X.map TrivSqZeroExt.inl *
      (1 - Y.map (TrivSqZeroExt.inr : O → DualNumber O))).map TrivSqZeroExt.snd = Y * X - X * Y := by
    rw [map_snd_mul_dualNumber_matrix, map_fst_mul_dualNumber_matrix, map_snd_mul_dualNumber_matrix, p1, p2, x1, x2, q1, q2]
    simp only [one_mul, mul_one, mul_zero, zero_add, mul_neg]
    abel
  exact ⟨congrFun (congrFun F a) b, congrFun (congrFun S a) b⟩

private theorem dU_res [IsLocalRing O] [IsCO O (DualNumber O)] (Y : M4 O) :
    (dU Y : M4 (DualNumber O)).map (res O (DualNumber O)) = 1 ∧
      (((dU Y)⁻¹ : (M4 (DualNumber O))ˣ) : M4 (DualNumber O)).map (res O (DualNumber O)) = 1 := by
  have hres : ∀ y : O, res O (DualNumber O) (TrivSqZeroExt.inr y) = 0 := by
    intro y
    have h2 : (res O (DualNumber O) (TrivSqZeroExt.inr y)) ^ 2 = 0 := by
      rw [← map_pow, pow_two]
      simp
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hE : (Y.map (TrivSqZeroExt.inr : O → DualNumber O)).map (res O (DualNumber O)) = 0 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.zero_apply, hres]
  constructor
  · rw [dU_val, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hE, add_zero]
  · rw [dU_inv, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), hE, sub_zero]

end Dual

private theorem cjL_hom_eq_conj {B : Type} [CommRing B] {O : Type} [CommRing O] [IsLocalRing O] [Algebra O B]
    [IsCO O B] {H : Type} [Group H] [TopologicalSpace H] {rb : H →* M4 (ResidueField O)} (h : (M4 B)ˣ)
    (h1 : (h : M4 B).map (res O B) = 1) (h2 : ((h⁻¹ : (M4 B)ˣ) : M4 B).map (res O B) = 1) (r : Lift O rb B) (g : H) :
    (cjL h h1 h2 r).hom g = h * r.hom g * (h⁻¹ : (M4 B)ˣ) := rfl

theorem UpperTheory.exists_local_first_order_lifts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ Y : D.T → M4 c.O, (∀ v, Y v ∈ sp4 c.O) → ∃ ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) (DualNumber c.O), D.LocEqs ρ ∧ ∀ (v : D.T) (g : D.Gp v) (a b : Fin 4), ((ρ v).hom g a b).fst = D.r0 g a b ∧ ((ρ v).hom g a b).snd = (Y v * D.r0 g - D.r0 g * Y v) a b := by
  intro Ω _ _ _ l _ c D hD Y hY
  obtain ⟨ρ₀, hhom, hpt⟩ := r0pt D hD
  have hL : D.condL (DualNumber c.O) (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ l)) := by
    obtain ⟨B, _, _, _, _, ρ, hPl, -, y, hy⟩ := hpt.atL
    rw [← hy]
    exact Ex.condL_map D (Algebra.ofId _ _) _ (Ex.condL_map D y ρ hPl)
  have hP : ∀ p ∈ D.Sb,
      D.condP p (DualNumber c.O) (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ p)) := by
    intro p hp
    obtain ⟨B, _, _, _, _, ρ, hPp, -, y, hy⟩ := hpt.atP p hp
    rw [← hy]
    exact Ex.condP_map D p (Algebra.ofId _ _) _ (Ex.condP_map D p y ρ hPp)
  refine ⟨fun v => cjL (dU (Y v)) (dU_res (Y v)).1 (dU_res (Y v)).2
    (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ v)), ⟨?_, ?_⟩, ?_⟩
  · exact ⟨fun g => gsp_conj (dU_adj (hY _)) (hL.1 g), ord_cj _ hL.2⟩
  · intro p hp
    refine ⟨fun g => gsp_conj (dU_adj (hY _)) ((hP p hp).1 g), fun g hg => ?_⟩
    show cj _ _ g = 1
    rw [cj_apply, (hP p hp).2 g hg, mul_one, Units.mul_inv]
  · intro v g a b
    have hX : ∀ a b, (Lift.map (Algebra.ofId c.O (DualNumber c.O)) (D.loc ρ₀ v)).hom g a b =
        TrivSqZeroExt.inl (D.r0 g a b) := by
      intro a b
      show algebraMap c.O (DualNumber c.O) (ρ₀.hom g a b) = _
      rw [hhom]
      rfl
    have key := dU_conj (Y v) (D.r0 g) _ hX a b
    simp only [cjL_hom_eq_conj]
    exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FlagL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.flagL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → ∃ κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ, Af.IsFlagOn r.toHomUnits (D.Gp l) κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.O) : PadicAlgCl l)) ∧ ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.O) : PadicAlgCl l)‖ < 1 := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
  obtain ⟨h, κ, hF, h1, h2, -⟩ := UpperTheory.V.Loc.spPtL D hD
    ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
    ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
  refine ⟨κ, ⟨h⁻¹, fun s => ?_⟩, h1, h2⟩
  rw [inv_inv]
  exact hF s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MPrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (I : Ideal O) (d : R →ₗ[O] O) (hd : d ∈ PtDer x O) (h0 : ∀ f, π f = 0 → d f ∈ I)
    (h1 : ∀ g i j, ∃ f, π f = r.hom g i j ∧ d f ∈ I) (f : R) : d f ∈ I := by
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl
  have hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I) := fun f g => by
    have := hd f g
    simp only [LinearMap.comp_apply, this, map_add (f := _), map_smul]
  obtain ⟨y, hy⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩
  obtain ⟨y', hy'⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩
  have key : ∀ f, d f ∈ I ↔ y f = y' f := fun f => by
    rw [TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]
    simp only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have k' : ∀ f, π f = 0 → y' f = 0 := fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)
  have k : ∀ f, π f = 0 → y f = 0 := fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  have he : ∀ f, e (π f) = Ideal.Quotient.mk _ f := fun f => by
    simp only [e]; rw [AlgEquiv.symm_apply_eq]; rfl
  let u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom
  let u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom
  have hu : ∀ f, u (π f) = y f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _
    rw [he]; rfl
  have hu' : ∀ f, u' (π f) = y' f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _
    rw [he]; rfl
  have huu : u = u' := hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by
    obtain ⟨f, hf, hf'⟩ := h1 g i j
    rw [Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))
  rw [key, ← hu, ← hu', huu]

private theorem wt_eq_neg (i j : Fin 4) : wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide

private theorem origin_part {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨p, hp, rfl⟩ := hf
  have := hp 0 (by rw [map_zero]; exact hj.symm)
  rw [AlgHom.toLinearMap_apply, WPres.origin_π]
  simpa using this

private theorem len_le (hM : LemmaM') {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (P : ℤ × ℤ → Submodule O R) (hom : ∀ g i j, ∃ f ∈ P (wt i j), π f = r.hom g i j)
    (A : Subalgebra O R) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (hA : ∀ n (f : A), f ∈ 𝒜 n ↔ f.1 ∈ P (0, n))
    (hA' : ∀ n f, f ∈ P (0, n) → f ∈ A) (hx1 : ∀ f ∈ P (0, -1), x f = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 (-1)) (hF0 : ∀ i, π (F i) = 0)
    (a : O) (ha : a ≠ 0) (N : Type) [AddCommGroup N] [Module O N] (Z : N →+ (Γ → O ⧸ Ideal.span {a}))
    (hZ : Function.Injective Z) (s t : Γ → Oˣ)
    (der : ∀ μ, ∃ δ ∈ PtDer x O, HasWt P (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = r.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (s g : O) * Z μ g) ∧
        (π f = r.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (t g : O) * Z μ g)) :
    Module.length O N ≤ cotLen (x.comp A.val) 𝒜 (-1) F := by
  choose δ h1 h2 h3 h4 using der
  have hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) =
      Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f) := fun μ ν f => by
    rw [← map_add (f := _), Ideal.Quotient.eq]
    refine der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν))
      (sub_mem (h1 _) (add_mem (h1 _) (h1 _)))
      (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f
    obtain ⟨f, hf, hf'⟩ := hom g i j
    refine ⟨f, hf', ?_⟩
    show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _
    by_cases hw : wt i j = -wPs
    · rw [← Ideal.Quotient.eq, map_add (f := _)]
      rcases wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add (f := _), Pi.add_apply, mul_add]
      · rw [(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add (f := _), Pi.add_apply, mul_add]
    · rw [h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]; simp
  let Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν =>
      LinearMap.ext fun f => hadd μ ν f
  have hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f) := fun _ _ => rfl
  refine hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_)
    fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩
  · refine (injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_
    rw [map_zero]
    funext g
    obtain ⟨f, hf, hf'⟩ := hom g 2 0
    have e1 := hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩
    rw [hμ, LinearMap.zero_apply, (h4 μ g f).1 hf'] at e1
    exact ((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm
  · rw [hDm, Ideal.Quotient.eq_zero_iff_mem]
    exact h3 μ _ (hF0 i)
  · exact h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.mPrime :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], LemmaM' → SoFin Ω l → D.sha ≤ cotLen M.x0 M.gr (-1) M.eqns.F := by
  intro Ω _ _ _ l _ c D hD M _ hM hS
  obtain ⟨-, a, ha, Z, hZ, hc⟩ := shaCoc D hD hS
  haveI : Finite (ResidueField c.O) := by
    obtain ⟨-, -, h, -⟩ := dvrFacts l c.O
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite ‹_›
  have hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0 := fun f hf => by
    obtain ⟨e, -, he⟩ := M.hom 1 0 0
    have h1 := M.at0 1 0 0 (f + e) (by rw [map_add (f := _), hf, he, zero_add])
    rw [map_add (f := _), M.at0 1 0 0 e he] at h1
    exact add_eq_right.1 h1
  set_option synthInstance.maxHeartbeats 200000 in
   exact len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl)
    (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF
    (fun i => by
      show M.F i ∈ RingHom.ker M.π
      rw [M.ker]
      exact Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)
end

