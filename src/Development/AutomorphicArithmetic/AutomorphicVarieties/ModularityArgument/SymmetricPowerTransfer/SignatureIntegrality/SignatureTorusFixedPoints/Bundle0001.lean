module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ConjDiag
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.conjDiag : UpperTheory.V.Z.Sym.Sig.ConjDiag := by
  intro k _ _ _ _ n s s' hs hs' y hy
  have hc : (dg s : GL (Fin n) k) * y = y * dg s' := by
    rw [← hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hM := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) hc
  simp only [Units.val_mul, UpperTheory.V.Z.Sym.Sig.dg, val_diagT] at hM
  have key : ∀ i j, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 → (s i : k) = s' j := by
    intro i j hij
    have e := congrFun (congrFun hM i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at e
    exact mul_left_cancel₀ hij e
  have hdet : (y : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have col : ∀ j, ∃ i, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 := by
    intro j
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero j h)
  choose σ hσ using col
  have hσs : ∀ j, (s (σ j) : k) = s' j := fun j => key _ _ (hσ j)
  have hmono : StrictMono σ := by
    intro j j' hjj'
    have h1 := hs' j j' hjj'
    rw [← hσs, ← hσs] at h1
    by_contra hle
    push_neg at hle
    rcases hle.lt_or_eq with h2 | h2
    · exact lt_irrefl _ (lt_trans h1 (hs _ _ h2))
    · rw [h2] at h1
      exact lt_irrefl _ h1
  have hid : σ = id := hmono.eq_id
  have hss : ∀ j, (s j : k) = s' j := by
    intro j
    have := hσs j
    rwa [hid] at this
  have inj : ∀ i j, (s i : k) = s j → i = j := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · have := hs i j hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
    · exact hij
    · have := hs j i hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
  have hdiag : ∀ i j, i ≠ j → (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
    intro i j hij
    by_contra h
    exact hij (inj i j ((key i j h).trans (hss j).symm))
  have hne : ∀ i, (y : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
    intro i
    have := hσ i
    rwa [hid] at this
  refine ⟨funext fun j => Units.ext (hss j), fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  simp only [UpperTheory.V.Z.Sym.Sig.dg, val_diagT, Units.val_mk0]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ s : K}

private theorem neg_sq (hs : s * s = Δ) : (-s) * (-s) = Δ := by rw [neg_mul_neg, hs]

private theorem proj_apply (hs : s * s = Δ) (x : Lsq K Δ) : proj hs x = x.re + s * x.im := rfl

private theorem proj_star (hs : s * s = Δ) (x : Lsq K Δ) : proj hs (star x) = proj (neg_sq hs) x := by
  simp [proj_apply]

private theorem proj_alg (hs : s * s = Δ) (a : K) : proj hs (algebraMap K (Lsq K Δ) a) = a := by
  simp [proj_apply]

private theorem proj_ext (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) {x y : Lsq K Δ}
    (e1 : proj hs x = proj hs y) (e2 : proj (neg_sq hs) x = proj (neg_sq hs) y) : x = y := by
  rw [proj_apply, proj_apply] at e1 e2
  have a : 2 * x.re = 2 * y.re := by linear_combination e1 + e2
  have b : (2 * s) * x.im = (2 * s) * y.im := by linear_combination e1 - e2
  ext
  · exact mul_left_cancel₀ h2 a
  · exact mul_left_cancel₀ (mul_ne_zero h2 h0) b

private def lft (s a b : K) : Lsq K Δ := ⟨(a + b) / 2, (a - b) / (2 * s)⟩

private theorem proj_lft (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (a b : K) :
    proj hs (lft s a b) = a := by
  rw [proj_apply]
  show (a + b) / 2 + s * ((a - b) / (2 * s)) = a
  field_simp
  ring

private theorem proj_lft' (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (a b : K) :
    proj (neg_sq hs) (lft s a b) = b := by
  rw [proj_apply]
  show (a + b) / 2 + -s * ((a - b) / (2 * s)) = b
  field_simp
  ring

private theorem eU_val (hs : s * s = Δ) (g : U3 Δ) :
    ((eU hs g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj hs) := rfl

private theorem eU_inv_apply (hs : s * s = Δ) (g : U3 Δ) (i j : Fin 3) :
    (((eU hs g)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      proj (neg_sq hs) ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) j i) := by
  rw [← map_inv, eU_val, Matrix.map_apply, ← proj_star]
  rfl

private theorem theta_val (g : U3 Δ) :
    ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := rfl

private theorem eU_theta (hs : s * s = Δ) (g : U3 Δ) : eU hs (theta Δ g) = th K 3 (eU hs g) := by
  ext i j
  rw [eU_val, theta_val]
  show _ = ((eU hs g)⁻¹ : GL (Fin 3) K) j i
  rw [eU_inv_apply, Matrix.map_apply, Matrix.map_apply, proj_star]

end Alg

section Alg2

variable {K : Type} [Field K] {Δ s : K}

private theorem proj_star' (hs : s * s = Δ) (x : Lsq K Δ) : proj (neg_sq hs) (star x) = proj hs x := by
  simp [proj_apply]

private theorem eU_inj (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) : Function.Injective (eU hs) := by
  intro g g' h
  refine Subtype.ext (Matrix.ext fun i j => proj_ext h2 h0 hs ?_ ?_)
  · have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j) h
    simpa only [eU_val, Matrix.map_apply] using this
  · have := congrArg (fun x : GL (Fin 3) K => ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j i) h
    simpa only [eU_inv_apply] using this

private theorem eU_surj (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) : Function.Surjective (eU hs) := by
  intro A
  set B : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hB
  let M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
    Matrix.of fun i j => lft s ((A : Matrix (Fin 3) (Fin 3) K) i j) (B j i)
  have p1 : M.map (proj hs) = (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    exact proj_lft h2 h0 hs _ _
  have p2 : M.map (proj (neg_sq hs)) = Bᵀ := by
    ext i j
    exact proj_lft' h2 h0 hs _ _
  have q1 : (star M).map (proj hs) = B := by
    ext i j
    rw [Matrix.map_apply, Matrix.star_apply, proj_star]
    have e := congrFun (congrFun p2 j) i
    simpa only [Matrix.map_apply, Matrix.transpose_apply] using e
  have q2 : (star M).map (proj (neg_sq hs)) = (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by
    ext i j
    rw [Matrix.map_apply, Matrix.star_apply, proj_star']
    have e := congrFun (congrFun p1 j) i
    simpa only [Matrix.map_apply, Matrix.transpose_apply] using e
  have hBA : B * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hB]
    exact A.inv_mul
  have e1 : (star M * M).map (proj hs) = (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj hs) := by
    rw [Matrix.map_mul, q1, p1, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (star M * M).map (proj (neg_sq hs)) =
      (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj (neg_sq hs)) := by
    rw [Matrix.map_mul, q2, p2, ← Matrix.transpose_mul, hBA, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : star M * M = 1 := by
    refine Matrix.ext fun i j => ?_
    apply proj_ext h2 h0 hs
    · have e := congrFun (congrFun e1 i) j
      simpa only [Matrix.map_apply] using e
    · have e := congrFun (congrFun e2 i) j
      simpa only [Matrix.map_apply] using e
  refine ⟨⟨M, (Matrix.mem_unitaryGroup_iff').2 hu⟩, ?_⟩
  apply Units.ext
  rw [eU_val]
  exact p1

private theorem hasTau_iff (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (δ : U3 Δ) (τ : K) :
    HasTau δ τ ↔ ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly =
      (X - 1) * (X ^ 2 - C τ * X + 1) := by
  set N : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hN
  set Q : K[X] := (X - 1) * (X ^ 2 - C τ * X + 1) with hQ
  have hQ' : ((X - 1) * (X ^ 2 - C (algebraMap K (Lsq K Δ) τ) * X + 1) : (Lsq K Δ)[X]) =
      Q.map (algebraMap K (Lsq K Δ)) := by
    simp [hQ]
  have hA : ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = N.map (proj hs) := by
    rw [← eU_theta, ← map_mul, eU_val]
  have htt : theta Δ (theta Δ δ) = δ := by
    apply Subtype.ext
    rw [theta_val, theta_val]
    refine Matrix.ext fun i j => ?_
    show star (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) = _
    exact star_star _
  have hθ : (theta Δ δ * δ : U3 Δ) = theta Δ (δ * theta Δ δ) := by
    rw [map_mul, htt]
  have hB : N.map (proj (neg_sq hs)) =
      ((eU hs (theta Δ δ) * eU hs δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← map_mul, eU_val, hθ, theta_val]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, proj_star]
  have h1 : N.charpoly.map (proj hs) =
      ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly := by
    rw [hA, Matrix.charpoly_map]
  have h2' : N.charpoly.map (proj (neg_sq hs)) =
      ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly := by
    rw [← Matrix.charpoly_map, hB, ← eU_theta, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm]
  show N.charpoly = _ ↔ _
  rw [hQ']
  constructor
  · intro h
    rw [← h1, h, Polynomial.map_map]
    have hc : (proj hs).comp (algebraMap K (Lsq K Δ)) = RingHom.id K := RingHom.ext (proj_alg hs)
    rw [hc, Polynomial.map_id]
  · intro h
    refine Polynomial.ext fun n => ?_
    rw [Polynomial.coeff_map]
    apply proj_ext h2 h0 hs
    · rw [proj_alg, ← Polynomial.coeff_map, h1, h]
    · rw [proj_alg, ← Polynomial.coeff_map, h2', h]

end Alg2

section Int

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {O : Type} [CommRing O] [Algebra O k] {Δ s : k}

private theorem val_of_int (hO : IsInts k O) {a : k} (h : IsIntegral O a) : valuation k a ≤ 1 := by
  have hv : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩
  exact hv.mem_of_integral h

private theorem proj_algO (hs : s * s = Δ) (r : O) : proj hs (algebraMap O (Lsq k Δ) r) = algebraMap O k r := by
  rw [IsScalarTower.algebraMap_apply O k (Lsq k Δ), proj_alg]

private theorem int_proj (hs : s * s = Δ) {x : Lsq k Δ} (h : IsIntegral O x) : IsIntegral O (proj hs x) := by
  have hc : (algebraMap O k).comp (RingHom.id O) = (proj hs).comp (algebraMap O (Lsq k Δ)) :=
    RingHom.ext fun r => (proj_algO hs r).symm
  exact IsIntegral.map_of_comp_eq (RingHom.id O) (proj hs) hc h

private theorem int_of_val (hO : IsInts k O) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) {x : Lsq k Δ}
    (e1 : valuation k (proj hs x) ≤ 1) (e2 : valuation k (proj (neg_sq hs) x) ≤ 1) : IsIntegral O x := by
  have hsum : valuation k (proj hs x + proj (neg_sq hs) x) ≤ 1 := (valuation k).map_add_le e1 e2
  have hprod : valuation k (proj hs x * proj (neg_sq hs) x) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' e1 e2
  obtain ⟨p, hp⟩ := RingHom.mem_range.1 ((hO.range _).2 hsum)
  obtain ⟨q, hq⟩ := RingHom.mem_range.1 ((hO.range _).2 hprod)
  refine ⟨X ^ 2 - C p * X + C q, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [IsScalarTower.algebraMap_apply O k (Lsq k Δ) p, IsScalarTower.algebraMap_apply O k (Lsq k Δ) q, hp, hq]
  apply proj_ext h2 h0 hs
  · simp only [map_add (f := _), map_sub, map_mul, map_pow, proj_alg, map_zero]
    ring
  · simp only [map_add (f := _), map_sub, map_mul, map_pow, proj_alg, map_zero]
    ring

private theorem comap_KO (hO : IsInts k O) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) :
    (KO k (Fin 3)).comap (eU hs) = KU O Δ := by
  ext g
  rw [Subgroup.mem_comap, GlAx.mem_KO, GlAx.bd_zero, GlAx.bd_zero]
  constructor
  · rintro ⟨hA, hB⟩
    have a1 : ∀ i j, valuation k (proj hs ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) ≤ 1 := fun i j => by
      have e := hA i j
      rw [eU_val, Matrix.map_apply, Valuation.mem_integer_iff] at e
      exact e
    have a2 : ∀ i j, valuation k (proj (neg_sq hs) ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) ≤ 1 := fun i j => by
      have e := hB j i
      rw [eU_inv_apply, Valuation.mem_integer_iff] at e
      exact e
    show ∀ i j, _ ∧ _
    refine fun i j => ⟨int_of_val hO h2 h0 hs (a1 i j) (a2 i j), int_of_val hO h2 h0 hs ?_ ?_⟩
    · rw [proj_star]
      exact a2 i j
    · rw [proj_star']
      exact a1 i j
  · intro hg
    have hg' : ∀ i j, IsIntegral O ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j) ∧
        IsIntegral O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) := hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [eU_val, Matrix.map_apply, Valuation.mem_integer_iff]
      exact val_of_int hO (int_proj hs (hg' i j).1)
    · rw [eU_inv_apply, ← proj_star hs, Valuation.mem_integer_iff]
      exact val_of_int hO (int_proj hs (hg' j i).2)

end Int

theorem eU_facts : EU := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs h0
  exact ⟨⟨eU_inj h2 h0 hs, eU_surj h2 h0 hs⟩, eU_theta hs, comap_KO hO h2 h0 hs, hasTau_iff h2 h0 hs⟩

end UpperTheory.V.Z.Sym.Sig

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.factJ : UpperTheory.V.Z.Sym.Sig.FactJ := by
  intro k _ _ _ _ V n
  constructor
  · have hm : ∀ {a b : GL (Fin n) k}, (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y) →
        (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, b = x * t * y) →
        ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a * b = x * t * y := by
      rintro _ _ ⟨x, hx, t, ht, y, hy, rfl⟩ ⟨x', hx', t', ht', y', hy', rfl⟩
      obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := (glIwa k n).swap V.c y hy x' hx'
      refine ⟨x * (t * x2 * t⁻¹), mul_mem hx ((glIwa k n).T_N t (V.levelTorus_le_torus ht) x2 hx2), t * s * t',
        mul_mem (mul_mem ht (V.Tc_le_TH hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
        mul_mem ((glIwa k n).T_Nm V.c t'⁻¹ (inv_mem (V.levelTorus_le_torus ht')) y2 hy2) hy', ?_⟩
      calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
        _ = _ := by rw [h]; group
    have h1 : ∀ a ∈ (glIwa k n).N, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨a, ha, 1, one_mem _, 1, one_mem _, by simp⟩
    have h2 : ∀ a ∈ V.TH n, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, a, ha, 1, one_mem _, by simp⟩
    have h3 : ∀ a ∈ (glIwa k n).Nm V.c, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, 1, one_mem _, a, ha, by simp⟩
    let K : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, g = x * t * y}
        mul_mem' := hm
        one_mem' := h1 1 (one_mem _)
        inv_mem' := by
          rintro _ ⟨x, hx, t, ht, y, hy, rfl⟩
          have := hm (h3 _ (inv_mem hy)) (hm (h2 _ (inv_mem ht)) (h1 _ (inv_mem hx)))
          simpa only [_root_.mul_inv_rev, Set.mem_setOf_eq] using this }
    exact fun g hg => (show V.J n ≤ K from sup_le (sup_le h1 h2) h3) hg
  · rintro m a ha a' ha' _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ b hb b' hb' h
    have hT : ∀ s : Fin n → kˣ, (∀ i, s i ∈ V.H) → dg s ∈ KO k (Fin n) := fun s h => V.J_le_KO (V.dg_mem h)
    have k1 := Kc_conj (mul_mem (hT s' fun i => hs' i trivial) (V.J_le_KO (V.Nm_le hb'))) h
    set κ := dg s' * b' * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ with hκ
    set l := dg s * (b * b'⁻¹) * (dg s')⁻¹ with hl
    have e : a⁻¹ * a' = l * κ := by
      have : l * κ = dg s * b * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ := by
        rw [hl, hκ]; group
      rw [this]; group
    have hl0 : l ∈ KO k (Fin n) := mul_mem (mul_mem (hT s fun i => hs i trivial) (V.J_le_KO (V.Nm_le (mul_mem hb (inv_mem hb')))))
      (inv_mem (hT s' fun i => hs' i trivial))
    have hl1 : ∀ i j, i < j → (l : Matrix (Fin n) (Fin n) k) i j = 0 := fun i j hij => by
      rw [hl, dg, dg, ← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul,
        (GlAx.mem_low.1 (mul_mem hb (inv_mem hb')).1).1 i j hij]
      simp
    have hu := mul_mem (inv_mem ha) ha'
    refine mem_Kc_of hu.2 fun i j => ?_
    rcases le_or_gt j i with hij | hij
    · rw [GlAx.up_sub_one hu.1 hij]; simp
    · have e2 : ((a⁻¹ * a').val - 1) i j = ∑ r, l.val i r * (κ.val - 1) r j := by
        rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, hl1 i j hij, one_apply_ne hij.ne, e,
          Units.val_mul]
      rw [e2]
      refine Valuation.map_sum_le _ fun r _ => ?_
      rw [map_mul]
      exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 hl0).1 i r) ((GlAx.mem_Kc.1 k1).1 r j)).trans_eq (one_mul _)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsOpenKc
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.isOpen_Kc (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have ho : IsOpen {x : k | valuation k x ≤ uniformizer k ^ (c : ℤ)} := by
    have h0 : IsOpen ((valuation k).integer : Set k) := Valuation.isOpen_integer
    convert h0.preimage (continuous_mul_const ((unif k ^ (-(c : ℤ)) : kˣ) : k)) using 1
    ext x
    change _ ↔ valuation k _ ≤ 1
    rw [map_mul, GlAx.val_zpow, _root_.zpow_neg, mul_inv_le_iff₀ (zpow_pos GlAx.unif_pos _), one_mul]
    rfl
  have h : ∀ f : GL (Fin n) k → GL (Fin n) k, Continuous f → IsOpen {g | GlAx.Bd c (f g)} := fun f hf => by
    simp only [GlAx.Bd, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (((Units.continuous_val.comp hf).sub continuous_const).matrix_elem i j)
  have : (Kc k n c : Set (GL (Fin n) k)) = {g | GlAx.Bd c (id g)} ∩ {g | GlAx.Bd c g⁻¹} := Set.ext fun g => GlAx.mem_Kc
  rw [this]
  exact (h _ continuous_id).inter (h _ continuous_inv)

theorem UpperTheory.V.Z.Sym.Sig.kc_sep {g : GL (Fin n) k} (h : ∀ m, g ∈ Kc k n m) : g = 1 := by
  refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_))
  by_contra h0
  have := (GlAx.mem_Kc.1 (h ((ord k (Units.mk0 _ h0)).natAbs + 1))).1 i j
  rw [show (g.val - 1) i j = (Units.mk0 _ h0 : kˣ) from rfl, val_ord,
    zpow_le_zpow_iff_right_of_lt_one₀ GlAx.unif_pos uniformizer_lt_one] at this
  omega

theorem UpperTheory.V.Z.Sym.Sig.kc_basis {S : Set (GL (Fin n) k)} (hS : S ∈ nhds (1 : GL (Fin n) k)) : ∃ m, (Kc k n m : Set (GL (Fin n) k)) ⊆ S := by
  by_contra hc
  push_neg at hc
  have hcl : ∀ m, IsClosed ((Kc k n m : Set (GL (Fin n) k)) \ interior S) := fun m =>
    ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).sdiff isOpen_interior
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun m => (Kc k n m : Set (GL (Fin n) k)) \ interior S)
    (fun m _ h => ⟨GlAx.Kc_anti (Nat.le_succ m) h.1, h.2⟩)
    (fun m => by obtain ⟨x, h1, h2⟩ := Set.not_subset.1 (hc m); exact ⟨x, h1, fun h => h2 (interior_subset h)⟩)
    (GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (hcl 0) fun _ h => GlAx.Kc_le 0 h.1) hcl
  have h1 : a = 1 := kc_sep fun m => (Set.mem_iInter.1 ha m).1
  exact (Set.mem_iInter.1 ha 0).2 (h1 ▸ mem_interior_iff_mem_nhds.2 hS)

end

theorem UpperTheory.V.Z.Sym.Sig.fixPt : UpperTheory.V.Z.Sym.Sig.FixPt := by
  intro k _ _ _ _ n Q hQ Ψ hΨ
  have hle : Q ≤ KO k (Fin n) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    exacts [fun _ h => h.2, fun _ h => GlAx.Kc_le _ h.2]
  have ce : ∀ i j, Continuous fun g : GL (Fin n) k => g.val i j := fun i j => Units.continuous_val.matrix_elem i j
  have hcl : IsClosed (Q : Set (GL (Fin n) k)) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    · have : (((glIwa k n).N : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : j < i), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ KO k (Fin n) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' (mem_unipB _)
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((KO k (Fin n)).isClosed_of_isOpen GlobalTheory.SplitFlip.isOpen_KO)
    · have : (((glIwa k n).Nm c : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : i < j), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ Kc k n (c + 1) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' GlAx.mem_low
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((Kc k n _).isClosed_of_isOpen (isOpen_Kc _))
  have hc : IsCompact (Q : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset hcl hle
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous Ψ := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    rw [ContinuousAt, Filter.tendsto_def]
    intro S hS
    obtain ⟨m, hm⟩ := kc_basis (S := (fun g : GL (Fin n) k => (Ψ a : GL (Fin n) k) * g) ⁻¹' {g | ∀ h : g ∈ Q, (⟨g, h⟩ : Q) ∈ S}) (by
      refine (continuous_const_mul _).continuousAt.preimage_mem_nhds ?_
      rw [mul_one]
      obtain ⟨W, hW, hW'⟩ := (mem_nhds_subtype _ _ _).1 hS
      exact Filter.mem_of_superset hW fun g hg h => hW' hg)
    have ho : IsOpen {b : Q | (a : GL (Fin n) k)⁻¹ * b ∈ Kc k n m} :=
      (isOpen_Kc m).preimage (continuous_const.mul continuous_subtype_val)
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun b hb => ?_
    have := hm (GlAx.Kc_anti (Nat.le_succ m) (hΨ m a b hb))
    simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
    exact this (Ψ b).2
  let C : ℕ → Set Q := fun m => {a | (a : GL (Fin n) k)⁻¹ * Ψ a ∈ Kc k n m}
  have hne : ∀ m, (C m).Nonempty := fun m => by
    induction m with
    | zero => exact ⟨1, by
        show _ ∈ Kc k n 0
        rw [GlAx.Kc_zero]; exact mul_mem (inv_mem (hle (1 : Q).2)) (hle (Ψ 1).2)⟩
    | succ m ih => obtain ⟨a, ha⟩ := ih; exact ⟨Ψ a, hΨ m _ _ ha⟩
  have hC : ∀ m, IsClosed (C m) := fun m => ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).preimage
    (continuous_subtype_val.inv.mul (continuous_subtype_val.comp hcont))
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun m _ h => GlAx.Kc_anti (Nat.le_succ m) h) hne (hC 0).isCompact hC
  refine ⟨a, Subtype.ext (inv_mul_eq_one.1 (kc_sep fun m => Set.mem_iInter.1 ha m)).symm⟩

end
end

