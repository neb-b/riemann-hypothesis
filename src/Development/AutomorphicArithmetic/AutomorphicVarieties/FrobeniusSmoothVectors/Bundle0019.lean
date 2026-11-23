module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothVectorFixedByOpenSubgroup
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smooth_vector_fixed_by_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ χ : F.Γ →* kˣ, χ F.c = -1 → (∀ v, ∃ s, χ (F.loc v s) ≠ 1) → Nontrivial (H1C F.loc (chRep χ) fun _ => ⊥) → ∃ x : F.Γ → k, IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + χ g * x h) ∧ x F.c = 0 ∧ (∀ v, ∃ Y : k, ∀ s, x (F.loc v s) = χ (F.loc v s) * Y - Y) ∧ ∃ g : F.G0, x g ≠ 0 := by
  intro l _ k _ _ F C₀ hok χ hc hloc hnt
  obtain ⟨q, hq⟩ := exists_ne (0 : H1C F.loc (chRep χ) fun _ => ⊥)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq
  obtain ⟨⟨x, y⟩, hz⟩ := z
  obtain ⟨hlc, hcoc, hlocz⟩ := hz
  simp only [chRep_apply] at hcoc
  simp only [chRep_apply, Submodule.mem_bot] at hlocz
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  have hx1 : x 1 = 0 := by
    have e := hcoc 1 1
    rw [mul_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  have hχ : ∀ s, (χ s : k) * x F.c = x (s * F.c) - x s := by
    intro s
    rw [hcoc]
    ring
  set X : k := -(x F.c) / 2 with hX
  set x' : F.Γ → k := fun s => x s - ((χ s : k) * X - X) with hx'
  have hform : x' = fun s => (x s + x (s * F.c) - x F.c) / 2 := by
    funext s
    simp only [hx', hX]
    rw [show x (s * F.c) = (χ s : k) * x F.c + x s by rw [hχ]; ring]
    field_simp
    ring
  have hcoc' : ∀ g h, x' (g * h) = x' g + (χ g : k) * x' h := by
    intro g h
    simp only [hx']
    rw [hcoc, map_mul, Units.val_mul]
    ring
  have hc' : x' F.c = 0 := by
    rw [hform]
    simp only
    rw [hok.c_sq, hx1]
    ring
  have hloc' : ∀ v s, x' (F.loc v s) = (χ (F.loc v s) : k) * (y v - X) - (y v - X) := by
    intro v s
    simp only [hx']
    have e := hlocz v s
    linear_combination e
  refine ⟨x', ?_, hcoc', hc', fun v => ⟨y v - X, hloc' v⟩, ?_⟩
  · rw [hform]
    exact IsLocallyConstant.comp₂ hlc (hlc.comp_continuous (continuous_mul_const F.c))
      (fun a b => (a + b - x F.c) / 2)
  · by_contra hall
    push_neg at hall
    have hzero : ∀ γ, x' γ = 0 := by
      intro γ
      rcases Int.units_eq_one_or (F.del γ) with hd | hd
      · exact hall ⟨γ, hd⟩
      · have hm : γ * F.c ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, hd, hok.del_c]
          rfl
        have e : γ = (γ * F.c) * F.c := by
          rw [mul_assoc, hok.c_sq, mul_one]
        rw [e, hcoc', hc', mul_zero, add_zero]
        exact hall ⟨_, hm⟩
    have hy : ∀ v, y v - X = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hloc v
      have e := hloc' v s
      rw [hzero] at e
      have e' : ((χ (F.loc v s) : k) - 1) * (y v - X) = 0 := by
        linear_combination -e
      rcases mul_eq_zero.1 e' with h | h
      · exact absurd (by
          have : (χ (F.loc v s) : k) = 1 := sub_eq_zero.1 h
          exact Units.val_eq_one.1 this) hs
      · exact h
    apply hq
    refine ⟨X, fun s => ?_, fun v => ?_⟩
    · have e := hzero s
      simp only [hx'] at e
      show x s = (chRep χ s) X - X
      rw [chRep_apply]
      linear_combination e
    · show y v - X ∈ (⊥ : Submodule k k)
      rw [Submodule.mem_bot]
      exact hy v
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZeroOfNeg
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem z2 (j : ZMod 2) : j = 0 ∨ j = 1 := by revert j; decide

private theorem sg_zero (K : Type) [CommRing K] : sg K 0 = 1 := pow_zero _

private theorem sg_one (K : Type) [CommRing K] : sg K 1 = -1 := pow_one _

private theorem pw_rev (a b : Fin 3) : pw b.rev a.rev = pw a b := by
  revert a b; decide

private theorem zero_of_neg {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {x : K} (h : x = -x) : x = 0 := by
  have : 2 * x = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

private def Dm (K : Type) [CommRing K] : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal fun a => sg K (pq a)

private theorem mem_iff {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X ∈ adp K j ↔ Dm K * X = sg K j • (X * Dm K) := by
  have hsq : ∀ y : ZMod 2, sg K y * sg K y = 1 := by
    intro y
    rcases z2 y with rfl | rfl <;> simp [sg_zero, sg_one]
  have hsub : ∀ x y : ZMod 2, sg K (x - y) = sg K x * sg K y := by
    intro x y
    rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl
    · simp [sg_zero]
    · rw [show (0 : ZMod 2) - 1 = 1 from rfl, sg_zero, sg_one, one_mul]
    · rw [show (1 : ZMod 2) - 0 = 1 from rfl, sg_zero, mul_one]
    · rw [show (1 : ZMod 2) - 1 = 0 from rfl, sg_zero, sg_one]
      norm_num
  constructor
  · intro hX
    ext a b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : pw a b = j
    · rw [← hab, pw_eq, hsub]
      linear_combination (-(sg K (pq a) * X a b)) * hsq (pq b)
    · have h0 : X a b = 0 := hX a b hab
      rw [h0]
      simp
  · intro h
    show ∀ a b, pw a b ≠ j → X a b = 0
    intro a b hab
    have e := congrFun (congrFun h a) b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e
    have hj : sg K j = -(sg K (pq a) * sg K (pq b)) := by
      rw [pw_eq] at hab
      generalize pq a = x at hab ⊢
      generalize pq b = y at hab ⊢
      rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl <;> rcases z2 j with rfl | rfl <;>
        first | exact absurd (by decide) hab | simp [sg_zero, sg_one]
    rw [hj] at e
    apply zero_of_neg h2
    linear_combination (sg K (pq a)) * e - (X a b + X a b * (sg K (pq b) * sg K (pq b))) * hsq (pq a) -
      X a b * hsq (pq b)

private theorem theta_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (h : X ∈ adp K j) : thetaLie X ∈ adp K j := by
  show ∀ a b, pw a b ≠ j → thetaLie X a b = 0
  intro a b hab
  have hX : X b.rev a.rev = 0 := h b.rev a.rev (by rw [pw_rev]; exact hab)
  have ht : thetaLie X a b = -X b.rev a.rev := by
    simp only [thetaLie, Matrix.neg_apply, Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul,
      zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [Finset.sum_eq_single b.rev]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hb
      exact hc (by rw [hb, Fin.rev_rev])
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [ht, hX, neg_zero]

private theorem conj_mem {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (g : GL (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) ∈ adp K 0) (j : ZMod 2) (Y : Matrix (Fin 3) (Fin 3) K)
    (h : Y ∈ adp K j) :
    (g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ adp K j := by
  rw [mem_iff h2] at hg h ⊢
  rw [sg_zero, one_smul] at hg
  have hgi : Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Dm K := by
    have e := congrArg (fun M => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hg
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc Dm K * ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = (Dm K * (g : Matrix (Fin 3) (Fin 3) K)) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (Dm K * Y) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hg]
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (sg K j • (Y * Dm K)) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y *
          (Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          simp only [mul_assoc]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Dm K) := by
          rw [hgi]
          simp only [mul_assoc]

theorem UpperTheory.V.Fr.ep_ev :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → (B.bar O).Ev π := by
  intro l _ k _ F O _ _ _ _ h2O R _ _ _ σ B π hG
  have h2 : (2 : ResidueField O) ≠ 0 := by
    have hu := h2O.map (IsLocalRing.residue O)
    rw [map_ofNat] at hu
    exact hu.ne_zero
  have key : ∀ x : R, ∀ j : ZMod 2, j ≠ 0 → x ∈ evp σ j → res O R x = 0 := by
    intro x j hj hx
    have hj1 : j = 1 := (z2 j).resolve_left hj
    subst hj1
    have e : σ x = sg R 1 * x := hx
    rw [sg_one, neg_one_mul] at e
    apply zero_of_neg h2
    have hm := UpperTheory.V.Alg.res_map (O := O) σ x
    rw [e, map_neg] at hm
    exact hm.symm
  have hr : ∀ s, ((B.bar O).r s).mat ∈ adp (ResidueField O) 0 := by
    intro s
    show ∀ a b, pw a b ≠ 0 → ((B.bar O).r s).mat a b = 0
    intro a b hab
    rw [pw_eq] at hab
    have := key _ _ hab (hG.r s a b)
    simpa [Box.bar, Box.map, GG.mat, GG.map] using this
  refine ⟨hr, ?_, ?_⟩
  · intro v a b hab
    have := key _ _ (sub_ne_zero.mpr hab) (hG.g v a b)
    simpa [Box.bar, Box.map] using this
  · intro j s X hX
    rw [Submodule.mem_comap]
    simp only [Box.ad, adRep, GG.ad, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, GG.adFun]
    apply conj_mem h2 _ (hr s) j
    split_ifs
    · exact hX
    · exact theta_mem j X hX
end

