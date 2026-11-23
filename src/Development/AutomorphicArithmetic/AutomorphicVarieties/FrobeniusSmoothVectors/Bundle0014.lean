module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDimb
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem db_inv {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (a b : Fin 3) (e : π a ≠ pq b) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b a = 0 := by
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h1 : u * g = 1 := g.inv_mul
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  let P : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if π i = π a then 1 else 0
  let Q : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if pq i = π a then 1 else 0
  have hc : P * g = g * Q := by
    ext i j
    simp only [P, Q, diagonal_mul, mul_diagonal]
    by_cases c : π i = pq j
    · rw [c, mul_comm]
    · rw [h i j c, mul_zero, zero_mul]
  have hd : u * P = Q * u := by
    calc u * P = u * (P * g) * u := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Q * u := by rw [hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have := congrFun (congrFun hd b) a
  simpa [P, Q, diagonal_mul, mul_diagonal, e.symm] using this

private theorem db_ex {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (b : Fin 3) : ∃ a, π a = pq b := by
  by_contra c
  push Not at c
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := g.inv_mul
  have := congrFun (congrFun h1 b) b
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => by rw [h a b (c a), mul_zero]] at this
  simp at this

private theorem db_card {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (j : ZMod 2) :
    Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} ≤
      Module.finrank K ((bor g).comap (adp K j).subtype) := by
  have h' := db_inv g π h
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  have hc : ∀ X : Matrix (Fin 3) (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (u * X * g) * u = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let f : {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} → (bor g).comap (adp K j).subtype := fun p =>
    ⟨⟨u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K), fun a b e => by
      have : (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) a b =
          u a p.1.1 * (g : Matrix (Fin 3) (Fin 3) K) p.1.2 b := by
        rw [Matrix.mul_apply, Finset.sum_eq_single p.1.2]
        · simp
        · intro c _ hc
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
        · simp
      rw [this]
      by_cases c : π p.1.1 = pq a
      · rw [h p.1.2 b fun c' => e (by rw [pw_eq, ← c, ← c', p.2.2]), mul_zero]
      · rw [h' _ _ c, zero_mul]⟩, by
      show UpT ((g : Matrix (Fin 3) (Fin 3) K) * (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) * u)
      rw [hc]
      intro a b e
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact absurd p.2.1 (not_le.2 e)⟩
  refine LinearIndependent.fintype_card_le_finrank (b := f) ?_
  let L : (bor g).comap (adp K j).subtype →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    (LinearMap.mulRight K u) ∘ₗ (LinearMap.mulLeft K (g : Matrix (Fin 3) (Fin 3) K)) ∘ₗ (adp K j).subtype ∘ₗ
      Submodule.subtype _
  refine LinearIndependent.of_comp L ?_
  have : L ∘ f = (Matrix.stdBasis K (Fin 3) (Fin 3)) ∘ Subtype.val := by
    funext p
    have := Matrix.stdBasis_eq_single (R := K) p.1.1 p.1.2
    exact (hc _).trans this.symm
  rw [this]
  exact (Matrix.stdBasis K (Fin 3) (Fin 3)).linearIndependent.comp _ Subtype.val_injective

private theorem db_counts : ∀ π : Fin 3 → ZMod 2, (∃ a, π a = 0) → (∃ a, π a = 1) →
    4 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 0} ∧
    2 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 1} := by
  decide +kernel

theorem UpperTheory.V.Fr.ep_dimb :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ v, 4 ≤ Module.finrank K (B.bp 0 v) ∧ 2 ≤ Module.finrank K (B.bp 1 v) := by
  intro l _ k _ F K _ _ B π h v
  have h0 : pq 1 = 0 := by decide
  have h1 : pq 0 = 1 := by decide
  obtain ⟨c0, c1⟩ := db_counts (π v) (h0 ▸ db_ex (B.g v) (π v) (h.g v) 1) (h1 ▸ db_ex (B.g v) (π v) (h.g v) 0)
  exact ⟨c0.trans (db_card (B.g v) (π v) (h.g v) 0), c1.trans (db_card (B.g v) (π v) (h.g v) 1)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDproj
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  simp only [sg, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

private theorem sg_sub (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i - j) = sg K i * sg K j := by
  have h : i - j = i + j := by revert i j; decide
  rw [h, sg_add]

private theorem sg_sq (K : Type) [CommRing K] (i : ZMod 2) : sg K i * sg K i = 1 := by
  have h : i + i = 0 := by revert i; decide
  rw [← sg_add, h]
  simp [sg]

private theorem sg_ne (K : Type) [CommRing K] (i j : ZMod 2) (e : i ≠ j) : sg K i * sg K j = -1 := by
  have h : i + j = 1 := by revert i j; decide
  rw [← sg_add, h]
  show (-1 : K) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

private theorem lin_sg {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup K] [Module O K]
    (D : R →ₗ[O] K) (i : ZMod 2) (x : R) : D (sg R i * x) = sg ℤ i • D x := by
  have h : i = 0 ∨ i = 1 := by revert i; decide
  rcases h with rfl | rfl
  · simp [sg]
  · show D ((-1 : R) ^ (1 : ZMod 2).val * x) = (-1 : ℤ) ^ (1 : ZMod 2).val • D x
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, pow_one, neg_one_mul, map_neg, neg_one_zsmul]

private theorem gl_inv_apply_eq_zero_of_forall_pw_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (G : GL (Fin 3) K)
    (hG : ∀ a b, pw a b ≠ 0 → (G : Matrix (Fin 3) (Fin 3) K) a b = 0) :
    ∀ a b, pw a b ≠ 0 → ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  set E : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun a => sg K (pq a)) with hE
  have hEE : E * E = 1 := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    simp only [sg_sq]
    exact Matrix.diagonal_one
  have hconj : ∀ (A : Matrix (Fin 3) (Fin 3) K) a b, (E * A * E) a b = sg K (pw a b) * A a b := by
    intro A a b
    rw [hE, Matrix.mul_diagonal, Matrix.diagonal_mul, pw_eq, sg_sub]
    ring
  have hEG : E * (G : Matrix (Fin 3) (Fin 3) K) * E = G := by
    ext a b
    rw [hconj]
    by_cases h : pw a b = 0
    · rw [h]
      simp [sg]
    · rw [hG a b h, mul_zero]
  have hinv1 : (G : Matrix (Fin 3) (Fin 3) K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) = 1 := by
      calc (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)
          = (E * (G : Matrix (Fin 3) (Fin 3) K) * E) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
            rw [hEG]
        _ = E * ((G : Matrix (Fin 3) (Fin 3) K) * ((E * E) * (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hEE, Matrix.one_mul, ← Matrix.mul_assoc (G : Matrix (Fin 3) (Fin 3) K), hinv1, Matrix.one_mul, hEE]
    calc E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E
        = (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
          rw [hinv2, Matrix.one_mul]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)) := by
          rw [Matrix.mul_assoc]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h1, Matrix.mul_one]
  intro a b hab
  have e := congrFun (congrFun key a) b
  rw [hconj] at e
  have hp : pw a b = 1 := by
    revert hab
    generalize pw a b = p
    revert p
    decide
  have s1 : sg K 1 = -1 := by
    show (-1 : K) ^ (1 : ZMod 2).val = -1
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
  rw [hp, s1] at e
  have e' : (2 : K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
    linear_combination -e
  exact (mul_eq_zero.mp e').resolve_left h2

theorem UpperTheory.V.Fr.ep_dproj :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → ∀ j, ∀ D ∈ Tan O R, ∃ D' ∈ derp O σ j, ∀ s, B.tanCo O D' s = prp (ResidueField O) j (B.tanCo O D s) := by
  intro l _ k _ F O _ _ h2 R _ _ _ σ hσ B π hB j D hD
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := h2.map (residue O)
    rw [map_ofNat] at this
    exact this.ne_zero
  have zs : ∀ (p : ZMod 2) (v : ResidueField O), sg ℤ p • v = sg (ResidueField O) p * v := by
    intro p v
    rw [zsmul_eq_mul]
    simp [sg]
  let D' : R →ₗ[O] ResidueField O :=
    (2 : ResidueField O)⁻¹ • (D + sg (ResidueField O) j • D.comp σ.toLinearMap)
  have hD' : ∀ x, D' x = (2 : ResidueField O)⁻¹ * (D x + sg (ResidueField O) j * D (σ x)) := by
    intro x
    simp [D', smul_eq_mul, mul_add]
  refine ⟨D', Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · intro f g
    have e1 := hD f g
    have e2 := hD (σ f) (σ g)
    rw [res_map, res_map] at e2
    rw [hD', hD', hD', map_mul σ f g, e1, e2]
    simp only [smul_eq_mul]
    ring
  · intro x
    show D' (σ x) = sg (ResidueField O) j * D' x
    rw [hD', hD', hσ]
    linear_combination (-(2 : ResidueField O)⁻¹ * D (σ x)) * sg_sq (ResidueField O) j
  · intro s
    have hM : ∀ a c, σ ((B.r s).mat a c) = sg R (pw a c) * (B.r s).mat a c := by
      intro a c
      rw [pw_eq]
      exact hB.r s a c
    have hDp : ∀ a c, D' ((B.r s).mat a c) = if pw a c = j then D ((B.r s).mat a c) else 0 := by
      intro a c
      rw [hD', hM, lin_sg, zs]
      split_ifs with hp
      · rw [hp]
        field_simp
        linear_combination D ((B.r s).mat a c) * sg_sq (ResidueField O) j
      · rw [← mul_assoc, sg_ne _ _ _ (Ne.symm hp)]
        ring
    have hbar : ∀ a c, pw a c ≠ 0 →
        (((Box.bar O B).r s).left : Matrix (Fin 3) (Fin 3) (ResidueField O)) a c = 0 := by
      intro a c hac
      show res O R ((B.r s).mat a c) = 0
      have hp : pw a c = 1 := by
        revert hac
        generalize pw a c = p
        revert p
        decide
      have e := congrArg (res O R) (hM a c)
      rw [res_map, hp, map_mul] at e
      have s1R : sg R 1 = -1 := by
        show (-1 : R) ^ (1 : ZMod 2).val = -1
        rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
      rw [s1R, map_neg, map_one] at e
      have e' : (2 : ResidueField O) * res O R ((B.r s).mat a c) = 0 := by
        linear_combination e
      exact (mul_eq_zero.mp e').resolve_left h2k
    have hN := gl_inv_apply_eq_zero_of_forall_pw_ne_zero h2k ((Box.bar O B).r s).left hbar
    ext a b
    show ((B.r s).mat.map D' * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b =
      if pw a b = j then ((B.r s).mat.map D * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b else 0
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hsame : ∀ c, pw c b = 0 → pw a c = pw a b := by
      intro c hcb
      rw [pw_eq] at hcb
      rw [pw_eq, pw_eq, sub_eq_zero.mp hcb]
    split_ifs with hab
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_pos ((hsame c hcb).trans hab)]
      · rw [hN c b hcb, mul_zero, mul_zero]
    · refine Finset.sum_eq_zero (fun c _ => ?_)
      rw [Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_neg (fun h => hab ((hsame c hcb).symm.trans h)), zero_mul]
      · rw [hN c b hcb, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpNosec
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ns_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (x : MvPowerSeries σ O) :
    x ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

private theorem ns_loc {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem ns_coeff {O σ : Type} [CommRing O] [DecidableEq σ] (s t : σ) (k : MvPowerSeries σ O) :
    MvPowerSeries.coeff (Finsupp.single s 1) (MvPowerSeries.X t * k) =
      if t = s then MvPowerSeries.constantCoeff k else 0 := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  by_cases h : t = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hle
    have := hle t
    simp [Finsupp.single_apply, Ne.symm h] at this

private theorem ns_dec {O σ : Type} [CommRing O] [IsLocalRing O] [Fintype σ] (g : MvPowerSeries σ O)
    (hg : ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) g ∈ maximalIdeal O) :
    ∃ k : σ → MvPowerSeries σ O, (∀ s, k s ∈ maximalIdeal (MvPowerSeries σ O)) ∧
      g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ s, MvPowerSeries.X s * k s := by
  classical
  obtain ⟨h, -, hh⟩ := GlobalTheory.exists_eq_sum_X_mul (n := 0)
    (g := g - algebraMap O _ (MvPowerSeries.constantCoeff g)) (by
      intro d hd
      have hd0 : d.degree = 0 := by omega
      have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst this
      simp [Algebra.algebraMap_eq_smul_one])
  have e : g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ i, MvPowerSeries.X i * h i := by
    rw [← hh]
    ring
  refine ⟨h, fun s => ?_, e⟩
  rw [ns_mem_max]
  have hs := hg s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_add (f := _), map_sum] at hs
  simp only [ns_coeff] at hs
  simpa [Algebra.algebraMap_eq_smul_one, MvPowerSeries.coeff_one] using hs

theorem UpperTheory.V.Fr.ep_nosec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι : Type) [Finite ι] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (π : MvPowerSeries ι O →ₐ[O] C) (p : C →ₐ[O] R) (s : R →ₐ[O] C), Function.Surjective π → IsMinPres (p.comp π) → (∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal C) → p.comp s = AlgHom.id O R → Function.Injective p := by
  intro O _ _ _ _ ι _ R _ _ _ C _ _ _ π p s hπ hmin hX hps
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : IsCO O O := ⟨‹IsAdicComplete (maximalIdeal O) O›, ⟨fun a ha => by simpa using ha⟩,
    fun x => ⟨x, by simp⟩⟩
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  have hq : ∀ x : C, p (s (p x)) = p x := fun x => by
    have := congrArg (fun φ : R →ₐ[O] R => φ (p x)) hps
    simpa using this
  have hE : ∀ x : C, x - s (p x) ∈ RingHom.ker p := fun x => by
    rw [RingHom.mem_ker, map_sub, hq, sub_self]
  have hloc : ∀ x : C, x ∈ maximalIdeal C → s (p x) ∈ maximalIdeal C := fun x hx =>
    (ns_loc s (p x)).2 ((ns_loc p x).2 hx)
  have hle : RingHom.ker p ≤ maximalIdeal C • RingHom.ker p := by
    intro t ht
    obtain ⟨g, rfl⟩ := hπ t
    have hpt : p (π g) = 0 := RingHom.mem_ker.mp ht
    have hg : g ∈ RingHom.ker (p.comp π) := by
      rw [RingHom.mem_ker, AlgHom.comp_apply, hpt]
    obtain ⟨k, hk, hgk⟩ := ns_dec g (hmin.2 g hg)
    have e : π g = π g - s (p (π g)) := by rw [hpt, map_zero, sub_zero]
    rw [e, hgk]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, AlgHom.commutes]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hk' : π (k i) ∈ maximalIdeal C := (ns_loc π (k i)).2 (hk i)
    have eq : π (MvPowerSeries.X i) * π (k i) - s (p (π (MvPowerSeries.X i))) * s (p (π (k i))) =
        π (k i) • (π (MvPowerSeries.X i) - s (p (π (MvPowerSeries.X i)))) +
          s (p (π (MvPowerSeries.X i))) • (π (k i) - s (p (π (k i)))) := by
      simp only [smul_eq_mul]
      ring
    rw [eq]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hk' (hE _))
      (Submodule.smul_mem_smul (hloc _ (hX i)) (hE _))
  have hbot : RingHom.ker p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal C) _ (IsNoetherian.noetherian _) hle
      (IsLocalRing.maximalIdeal_le_jacobson _)
  exact (RingHom.injective_iff_ker_eq_bot p).2 hbot
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpRels
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_rels :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2) (J : Ideal (MvPowerSeries ι O)), IsHomog O wt J → ∃ (κ : Type) (_ : Fintype κ) (f : κ → MvPowerSeries ι O) (wf : κ → ZMod 2), (∀ u, f u ∈ wtPart O wt (wf u)) ∧ J = Ideal.span (Set.range f) ∧ ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries ι O) * J → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 ι _ wt J hJ
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  obtain ⟨τ, hττ, hev, hw⟩ := ep_ps O h2 ι wt
  have hτJ : ∀ y ∈ J, τ y ∈ J := by
    intro y hy
    have e := hw 1 y
    have hs : sg (MvPowerSeries ι O) 1 = -1 := by
      simp only [sg]
      rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    rw [hs] at e
    have : τ y = y - 2 * wcomp O wt 1 y := by linear_combination e
    rw [this]
    exact J.sub_mem hy (J.mul_mem_left 2 (hJ y hy 1))
  have hτm : ∀ y ∈ maximalIdeal (MvPowerSeries ι O), τ y ∈ maximalIdeal (MvPowerSeries ι O) := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    rw [← hττ y]
    exact hu.map τ
  have hτN : ∀ y ∈ maximalIdeal (MvPowerSeries ι O) * J,
      τ y ∈ maximalIdeal (MvPowerSeries ι O) * J := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm j hj
      rw [map_mul]
      exact Ideal.mul_mem_mul (hτm m hm) (hτJ j hj)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb
  obtain ⟨a, g, z, hz, hle, hmin⟩ :=
    ep_basis O h2 (MvPowerSeries ι O) τ hττ J (maximalIdeal (MvPowerSeries ι O) * J) hτJ hτN le_rfl
  refine ⟨Fin a ⊕ Fin g, inferInstance, z, Space.Loc.par a g, ?_, ?_, hmin⟩
  · intro s
    rw [← hev]
    exact (hz s).2
  · apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J)
        (maximalIdeal_le_jacobson _)
      exact hle
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact (hz s).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpUpt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_upt :
    ∀ {C : Type} [CommRing C] {n : ℕ} (h T T' : Matrix (Fin n) (Fin n) C), UpT T → UpT T' → (∀ i j, j < i → IsUnit (T j j - T' i i)) → h * T = T' * h → UpT h := by
  intro C _ n h T T' hT hT' hu hc
  suffices key : ∀ m, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → h i j = 0 by
    intro i j hji
    exact key _ i j rfl hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    have e := congrFun (congrFun hc i) j
    simp only [Matrix.mul_apply] at e
    have hji' := Fin.lt_iff_val_lt_val.mp hji
    have L : ∑ k, h i k * T k j = h i j * T j j := by
      rw [Finset.sum_eq_single j]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hk | hk
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          rw [ih (k.val + (n - i.val)) (by omega) i k rfl (hk.trans hji), zero_mul]
        · rw [hT k j hk, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ j) hn
    have R : ∑ k, T' i k * h k j = T' i i * h i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hT' i k hk, zero_mul]
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          have hkn := k.isLt
          rw [ih (j.val + (n - k.val)) (by omega) k j rfl (hji.trans hk), mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ i) hn
    rw [L, R] at e
    have e2 : h i j * (T j j - T' i i) = 0 := by
      rw [mul_sub, e, mul_comm]
      exact sub_self _
    exact (hu i j hji).mul_left_eq_zero.mp e2
end

