module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisFDistribution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PsumGaloisUnitPiece
section
open GlobalTheory.KummerEisensteinGalois

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

lemma eisF_pow_subst {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    eisF j M (ζ ^ e) a₁ a₂ n = eisF j M ζ a₁ ((e : ℤ) * a₂) n := by
  have h : ∀ x : ℤ, (ζ ^ e) ^ x = ζ ^ ((e : ℤ) * x) := by
    intro x; rw [← zpow_natCast, ← zpow_mul]
  simp only [eisF, const0, coefPos, h, mul_assoc, mul_neg]

lemma smF_pow_subst {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    smF c j M (ζ ^ e) a₁ a₂ n = smF c j M ζ a₁ ((e : ℤ) * a₂) n := by
  simp only [smF, eisF_pow_subst]
  rw [mul_left_comm]

lemma eisF_congr {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ a₁ a₂' n := by
  have h1 : ζ ^ a₂ = ζ ^ a₂' := zpow_congr_of_modEq hζ hM h
  simp only [eisF, const0, coefPos, zpow_neg, zpow_mul, h1]

lemma smF_congr {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    smF c j M ζ a₁ a₂ n = smF c j M ζ a₁ a₂' n := by
  simp only [smF, eisF_congr j M ζ hζ hM a₁ a₂ a₂' h, eisF_congr j M ζ hζ hM _ _ _ (h.mul_left c)]

def diagOneUnit {R : Type} [CommRing R] (b : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![1, (b : R)], Matrix.diagonal ![1, ((b⁻¹ : Rˣ) : R)],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩

lemma diagOneUnit_mul {R : Type} [CommRing R] (a b : Rˣ) : diagOneUnit a * diagOneUnit b = diagOneUnit (a * b) := by
  ext i j
  simp only [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Units.val_mk, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

lemma diagOneUnit_one {R : Type} [CommRing R] : diagOneUnit (1 : Rˣ) = 1 := by
  ext i j
  simp only [diagOneUnit, Units.val_mk, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma coe_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) (i : Fin 2) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = (γ : Matrix (Fin 2) (Fin 2) R) i 0 ∧
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (γ : Matrix (Fin 2) (Fin 2) R) i 1 * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_diagonal]

lemma det_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (γ : Matrix (Fin 2) (Fin 2) R).det * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]

lemma smF_rowT_subst {K : Type} [Field K] [CharZero K] (N p m : ℕ) [NeZero p] (c : ℤ) (j : ℕ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (hN : 0 < N) (γ : GL (Fin 2) (ZMod (p ^ m))) (b : (ZMod (p ^ m))ˣ) (e : ℕ)
    (he : ((e : ℕ) : ZMod (p ^ m)) = b ∧ ((e : ℕ) : ZMod N) = 1) (i : Fin 2) (w : ℤ × ℤ) :
    smF c j (N * p ^ m) (ζ ^ e) (rowT N p m γ i w).1 (rowT N p m γ i w).2 =
      smF c j (N * p ^ m) ζ (rowT N p m (γ * diagOneUnit b) i w).1 (rowT N p m (γ * diagOneUnit b) i w).2 := by
  funext n
  rw [smF_pow_subst]
  have h1 : (rowT N p m (γ * diagOneUnit b) i w).1 = (rowT N p m γ i w).1 := by
    simp [rowT, (coe_mul_diagOneUnit γ b i).1]
  rw [h1]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply smF_congr c j _ ζ hζ (by positivity)
  simp only [rowT, (coe_mul_diagOneUnit γ b i).2]
  rw [Int.modEq_iff_dvd]
  have h2 : ((p ^ m : ℕ) : ℤ) ∣ (e : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1).val : ℤ) -
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1 * b).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [he.1, mul_comm]
  have h3 : (N : ℤ) ∣ (e : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [he.2, sub_self]
  obtain ⟨u, hu⟩ := h2
  obtain ⟨v, hv⟩ := h3
  refine ⟨-(u + w.2 * v), ?_⟩
  push_cast at hu ⊢
  linear_combination (-(N : ℤ)) * hu - ((p : ℤ) ^ m * w.2) * hv

theorem psum_galois_unitPiece : ∀ (N p m k : ℕ) [NeZero p] (K : Type) [Field K] [CharZero K]
    (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (β : (ZMod (p ^ m))ˣ → ℕ), p.Prime → 0 < N → Nat.Coprime p N → 1 ≤ m → IsPrimitiveRoot ζ (N * p ^ m) →
    (∀ b, ((β b : ℕ) : ZMod (p ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
    ∀ r : ℕ, ∑ b : (ZMod (p ^ m))ˣ, ψ b * pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' (ζ ^ β b)
        ((unitSet p m).filter (fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det = 1)) r =
      pieceT N p m m k ψ c d w w' ζ (unitSet p m) r := by
  intro N p m k _ K _ _ ψ c d w w' ζ β _ hN _ _ hζ hβ r
  unfold pieceT
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun x => x.2 * diagOneUnit x.1)
    (fun γ => (Matrix.GeneralLinearGroup.det γ, γ * diagOneUnit (Matrix.GeneralLinearGroup.det γ)⁻¹))
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ b 0).1, (coe_mul_diagOneUnit γ b 1).1]
    exact h.1
  · intro γ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ _ 0).1, (coe_mul_diagOneUnit γ _ 1).1]
    refine ⟨h, ?_⟩
    rw [det_mul_diagOneUnit, ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hd : Matrix.GeneralLinearGroup.det (γ * diagOneUnit b) = b := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, det_mul_diagOneUnit, h.2, one_mul]
    simp only [hd, mul_assoc, diagOneUnit_mul, mul_inv_cancel, diagOneUnit_one, mul_one]
  · intro γ _
    simp only [mul_assoc, diagOneUnit_mul, inv_mul_cancel, diagOneUnit_one, mul_one]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    dsimp only
    rw [smF_rowT_subst N p m c (k - 1) ζ hζ hN γ b (β b) (hβ b) 0 w,
      smF_rowT_subst N p m d 1 ζ hζ hN γ b (β b) (hβ b) 1 w', det_mul_diagOneUnit, h.2, one_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, map_one, one_mul]
    ring

end GlobalTheory.KummerEisensteinGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Hol

theorem differentiable_ee : Differentiable ℂ ee := by
  unfold ee
  exact (differentiable_id.const_mul _).cexp

theorem differentiableOn_geomProd {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    DifferentiableOn ℂ (fun z => ∏' m : ℕ, (1 - ee z ^ (m + 1) * g z)) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hec : Continuous ee := differentiable_ee.continuous
  have hgc : Continuous g := hg.continuous
  have hloc : HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 + -(ee z ^ (m + 1) * g z))
      (fun z => ∏' m : ℕ, (1 + -(ee z ^ (m + 1) * g z))) {z : ℂ | 0 < z.im} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K hK hKc => ?_
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · subst hK0
      exact Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun _ => (0 : ℝ)) summable_zero
        (.of_forall fun n z hz => absurd hz (Set.notMem_empty z))
        (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (continuous_norm.comp hec).continuousOn
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgc.continuousOn
    set r := ‖ee z₀‖ with hr_def
    have hr1 : r < 1 := norm_ee_lt_one ⟨z₀, hK hz₀⟩
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr : ∀ z ∈ K, ‖ee z‖ ≤ r := fun z hz => hmax hz
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
    refine Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun n => C * r * r ^ n)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (C * r)) (.of_forall fun n z hz => ?_)
      (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    rw [norm_neg, norm_mul, norm_pow]
    calc ‖ee z‖ ^ (n + 1) * ‖g z‖ ≤ r ^ (n + 1) * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hr z hz) _) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 _)
      _ = C * r * r ^ n := by ring
  have hd := hloc.differentiableOn (.of_forall fun n => by
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
      ((differentiable_const (1 : ℂ)).add ((differentiable_ee.pow (i + 1)).mul hg).neg).differentiableOn)) hU
  refine hd.congr fun z _ => ?_
  simp only [sub_eq_add_neg]

def geomProd (q a : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * a)

theorem tprod_cthFac {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ ≠ 0 ∧
    ∏' m : ℕ, cthFac c (ee τ) (ee (pt x τ)) (m + 1) =
      geomProd (ee τ) (ee (pt x τ)) ^ (c ^ 2) * geomProd (ee τ) (ee (pt x τ))⁻¹ ^ (c ^ 2) /
        (geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹) := by
  obtain ⟨hc1, hc6, hnot⟩ := h
  have hq : ‖ee τ‖ < 1 := norm_ee_lt_one τ
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact hnot ⟨⟨(c : ℤ) * a, by push_cast; rw [ha]⟩, ⟨(c : ℤ) * b, by push_cast; rw [hb]⟩⟩
  have hcx : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa [nsmul_eq_mul] using hnot
  have htc : ee (pt x τ) ^ c = ee (pt (c • x) τ) := ee_pt_pow c x τ
  have n1 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).1
  have n2 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ))⁻¹ ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).2
  have n3 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ^ c ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).1
  have n4 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ) ^ c)⁻¹ ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).2
  obtain ⟨P1, -, h1⟩ := hasProd_geom hq _ n1
  obtain ⟨P2, -, h2⟩ := hasProd_geom hq _ n2
  obtain ⟨P3, hP3, h3⟩ := hasProd_geom hq _ n3
  obtain ⟨P4, hP4, h4⟩ := hasProd_geom hq _ n4
  have e1 : geomProd (ee τ) (ee (pt x τ)) = P1 := h1.tprod_eq
  have e2 : geomProd (ee τ) (ee (pt x τ))⁻¹ = P2 := h2.tprod_eq
  have e3 : geomProd (ee τ) (ee (pt x τ) ^ c) = P3 := h3.tprod_eq
  have e4 : geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ = P4 := h4.tprod_eq
  rw [e1, e2, e3, e4]
  refine ⟨mul_ne_zero hP3 hP4, ?_⟩
  have hall := ((hasProd_pow h1 (c ^ 2)).mul (hasProd_pow h2 (c ^ 2))).mul
    (hasProd_inv (h3.mul h4) (mul_ne_zero hP3 hP4))
  rw [div_eq_mul_inv, ← hall.tprod_eq]
  refine tprod_congr fun m => ?_
  unfold cthFac
  rw [div_eq_mul_inv]

end GlobalTheory.Sieg.Hol

namespace GlobalTheory.Sieg

open Hol

theorem mdifferentiable_sg :
    ∀ (c : ℕ) (x : Fin 2 → ℚ), admitted c x → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sg c x) := by
  intro c x h
  rw [UpperHalfPlane.mdifferentiable_iff]
  set T : ℂ → ℂ := fun z => ee ((x 0 : ℂ) * z + (x 1 : ℂ)) with hT
  have hTd : Differentiable ℂ T := differentiable_ee.comp ((differentiable_id.const_mul _).add_const _)
  have hT0 : ∀ z, T z ≠ 0 := fun z => ee_ne_zero _
  have hG1 := differentiableOn_geomProd hTd
  have hG2 := differentiableOn_geomProd (hTd.inv hT0)
  have hG3 := differentiableOn_geomProd (hTd.pow c)
  have hG4 := differentiableOn_geomProd ((hTd.pow c).inv fun z => pow_ne_zero _ (hT0 z))
  have hnd : ∀ z ∈ {z : ℂ | 0 < z.im}, 1 - T z ^ c ≠ 0 := fun z hz =>
    (multipliable_and_sg_ne_zero h ⟨z, hz⟩).2.1
  have hnG : ∀ z ∈ {z : ℂ | 0 < z.im}, geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹ ≠ 0 :=
    fun z hz => (tprod_cthFac h ⟨z, hz⟩).1
  have hH : DifferentiableOn ℂ (fun z => ee z ^ ((c ^ 2 - 1) / 12) * (-T z) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (1 - T z) ^ (c ^ 2) / (1 - T z ^ c) *
      (geomProd (ee z) (T z) ^ (c ^ 2) * geomProd (ee z) (T z)⁻¹ ^ (c ^ 2) /
        (geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹))) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.mul (DifferentiableOn.div (DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_) ?_ hnd)
      (DifferentiableOn.div (DifferentiableOn.mul (hG1.pow _) (hG2.pow _)) (hG3.mul hG4) hnG)
    · exact (differentiable_ee.pow _).differentiableOn
    · exact hTd.neg.differentiableOn.zpow (Or.inl fun z _ => neg_ne_zero.mpr (hT0 z))
    · exact (((differentiable_const _).sub hTd).pow _).differentiableOn
    · exact ((differentiable_const _).sub (hTd.pow c)).differentiableOn
  refine hH.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold sg cth
  rw [(tprod_cthFac h ⟨z, hz'⟩).2]
  rfl

end GlobalTheory.Sieg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxSumRowLiftsDistribution
section
noncomputable section

open Finset GlobalTheory.KummerEisensteinGalois
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.RowFibre

theorem val_lift (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n)) (s : ℕ) (hs : s < p) :
    ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))).val = x.val + p ^ n * s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply ZMod.val_cast_of_lt
  have hx := ZMod.val_lt x
  calc x.val + p ^ n * s < p ^ n + p ^ n * s := by omega
    _ = p ^ n * (s + 1) := by ring
    _ ≤ p ^ n * p := Nat.mul_le_mul_left _ hs
    _ = p ^ (n + 1) := by ring

theorem sum_lifts {α : Type*} [AddCommMonoid α] (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n))
    (f : ZMod (p ^ (n + 1)) → α) :
    ∑ y ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x)), f y
      = ∑ s ∈ range p, f ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpos : 0 < p ^ n := pow_pos hp.out.pos n
  have hmem : ∀ y : ZMod (p ^ (n + 1)),
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x ↔ y.val % p ^ n = x.val := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    constructor
    · rintro rfl; rw [ZMod.val_natCast]
    · intro h; rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]
  symm
  refine Finset.sum_nbij' (fun s => ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))))
    (fun y => y.val / p ^ n) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hs ⊢
    rw [hmem, val_lift p n x s hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  · intro y hy
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hy ⊢
    rw [Nat.div_lt_iff_lt_mul hpos]
    have := ZMod.val_lt y
    calc y.val < p ^ (n + 1) := this
      _ = p * p ^ n := by ring
  · intro s hs
    simp only [mem_coe, mem_range] at hs
    rw [val_lift p n x s hs, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (ZMod.val_lt x), zero_add]
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy
    rw [hmem] at hy
    rw [← hy, Nat.mod_add_div, ZMod.natCast_zmod_val]
  · intro s _
    rfl

theorem sum_range_perm {α : Type*} [AddCommMonoid α] (p : ℕ) [hp : Fact p.Prime] (H : ℤ → α)
    (hH : ∀ t, H t = H (t % p)) (c e : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ∑ s ∈ range p, H (c * ((s : ℤ) + e)) = ∑ k ∈ range p, H k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set Hz : ZMod p → α := fun z => H (z.val : ℤ) with hHz
  have hHt : ∀ t : ℤ, H t = Hz (t : ZMod p) := by
    intro t; rw [hH t, hHz]; simp only [ZMod.val_intCast]
  have hr : ∀ f : ZMod p → α, ∑ s ∈ range p, f (s : ZMod p) = ∑ z, f z := by
    intro f
    refine Finset.sum_nbij' (fun s => (s : ZMod p)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
    · intros; simp
    · intro z _; simp [ZMod.val_lt]
    · intro s hs
      simp only [mem_coe, mem_range] at hs
      simp [ZMod.val_cast_of_lt hs]
    · intro z _; simp
    · intros; rfl
  have hcz : (c : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hbij : Function.Bijective (fun z : ZMod p => (c : ZMod p) * (z + e)) := by
    rw [← Finite.injective_iff_bijective]
    intro a b h
    simpa using mul_left_cancel₀ hcz h
  calc ∑ s ∈ range p, H (c * ((s : ℤ) + e))
        = ∑ s ∈ range p, Hz ((c : ZMod p) * ((s : ZMod p) + e)) := by
        refine sum_congr rfl fun s _ => ?_
        rw [hHt]; push_cast; rfl
    _ = ∑ z, Hz ((c : ZMod p) * (z + e)) := hr (fun z => Hz ((c : ZMod p) * (z + e)))
    _ = ∑ z, Hz z := Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    _ = ∑ k ∈ range p, Hz (k : ZMod p) := (hr Hz).symm
    _ = ∑ k ∈ range p, H k := by
        refine sum_congr rfl fun k _ => ?_
        rw [hHt]; push_cast; rfl

theorem modEq_shift (p M : ℕ) (A t : ℤ) :
    A + (M : ℤ) * t ≡ A + (M : ℤ) * (t % p) [ZMOD ((p * M : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-(t / p), ?_⟩
  push_cast
  linear_combination (M : ℤ) * Int.emod_add_mul_ediv t p

theorem sum_perm2 {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime] (M j : ℕ) (hM : 0 < M)
    (ζ : K) (hζ : ζ ^ (p * M) = 1) (A₁ A₂ c e₁ e₂ : ℤ) (hc : ¬ (p : ℤ) ∣ c) (r : ℕ) :
    ∑ s₁ ∈ range p, ∑ s₂ ∈ range p,
        eisF j (p * M) ζ (A₁ + M * (c * ((s₁ : ℤ) + e₁))) (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * i₁) (A₂ + M * i₂) r := by
  have hL : 0 < p * M := Nat.mul_pos hp.out.pos hM
  have inner : ∀ a : ℤ, ∑ s₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * i₂) r := by
    intro a
    exact sum_range_perm p (fun t => eisF j (p * M) ζ a (A₂ + M * t) r)
      (fun t => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ (Int.ModEq.refl a)
        (modEq_shift p M A₂ t)) r) c e₂ hc
  simp only [inner]
  exact sum_range_perm p (fun t => ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * t) (A₂ + M * i₂) r)
    (fun t => sum_congr rfl fun i₂ _ => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ
      (modEq_shift p M A₁ t) (Int.ModEq.refl _)) r) c e₁ hc

theorem not_dvd_num (p : ℕ) [hp : Fact p.Prime] (N n : ℕ) (hn : 1 ≤ n) (hpN : ¬ p ∣ N) (x : ℕ)
    (hx : ¬ p ∣ x) (w c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * ((N : ℤ) * x + (p : ℤ) ^ n * w)) := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpn : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ (by omega)
  have h1 : (p : ℤ) ∣ ((N * p ^ n : ℕ) : ℤ) := by
    push_cast; exact Dvd.dvd.mul_left hpn _
  rcases hpz.dvd_or_dvd (h1.trans h) with h3 | h3
  · exact hc h3
  · have h4 : (p : ℤ) ∣ (N : ℤ) * x := (dvd_add_left (Dvd.dvd.mul_right hpn w)).mp h3
    rcases hpz.dvd_or_dvd h4 with h5 | h5
    · exact hpN (Int.natCast_dvd_natCast.mp h5)
    · exact hx (Int.natCast_dvd_natCast.mp h5)

theorem smF_sum_lifts : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K) (c : ℤ)
    (x₁ x₂ : ZMod (p ^ n)) (u₁ u₂ w₁ w₂ : ℤ), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ n →
    1 ≤ j → ¬ (p : ℤ) ∣ c → ¬ p ∣ x₁.val → (p : ℤ) * u₁ ≡ w₁ [ZMOD N] → (p : ℤ) * u₂ ≡ w₂ [ZMOD N] →
    ∀ r : ℕ, ∑ y₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₁)),
      ∑ y₂ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₂)),
      smF c j (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁.val : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * (y₂.val : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r =
      (p : K) ^ ((2 : ℤ) - (j : ℤ)) * vp p (smF c j (N * p ^ n) (ζ ^ p) ((N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁)
        ((N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂)) r := by
  intro p hp N n j K _ _ ζ c x₁ x₂ u₁ u₂ w₁ w₂ hζ hN hpN hn hj hc hx hu₁ hu₂ r
  have hpos : 0 < p := hp.out.pos
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hpos n)
  have hL : N * p ^ (n + 1) = p * (N * p ^ n) := by ring
  have hζ' : IsPrimitiveRoot ζ (p * (N * p ^ n)) := hL ▸ hζ
  have hζ1 : ζ ^ (p * (N * p ^ n)) = 1 := hζ'.pow_eq_one
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨k₁, hk₁⟩ := hu₁.dvd
  obtain ⟨k₂, hk₂⟩ := hu₂.dvd
  set A₁ : ℤ := (N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁ with hA₁
  set A₂ : ℤ := (N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂ with hA₂
  rw [hL, sum_lifts p n x₁]
  simp_rw [sum_lifts p n x₂]
  have key : ∀ s₁ ∈ range p, ∀ s₂ ∈ range p,
      smF c j (p * (N * p ^ n)) ζ
        ((N : ℤ) * ((((x₁.val + p ^ n * s₁ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * ((((x₂.val + p ^ n * s₂ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r
      = (c : K) ^ 2 * eisF j (p * (N * p ^ n)) ζ (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
            (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂))) r
        - (c : K) ^ ((2 : ℤ) - j) * eisF j (p * (N * p ^ n)) ζ (c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)))
            (c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂))) r := by
    intro s₁ hs₁ s₂ hs₂
    rw [mem_range] at hs₁ hs₂
    rw [val_lift p n x₁ s₁ hs₁, val_lift p n x₂ s₂ hs₂]
    have e₁ : (N : ℤ) * ((x₁.val + p ^ n * s₁ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁
        = A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)) := by
      rw [hA₁]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₁
    have e₂ : (N : ℤ) * ((x₂.val + p ^ n * s₂ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂
        = A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)) := by
      rw [hA₂]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₂
    have f₁ : c * (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
        = c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)) := by ring
    have f₂ : c * (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)))
        = c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂)) := by ring
    rw [e₁, e₂, smF, f₁, f₂]
  refine (sum_congr rfl fun s₁ hs₁ => sum_congr rfl fun s₂ hs₂ => key s₁ hs₁ s₂ hs₂).trans ?_
  simp only [sum_sub_distrib, ← mul_sum]
  have h1 : ¬ (p : ℤ) ∣ 1 := hpz.not_dvd_one
  have nd₁ : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ A₂) := fun h => by
    have := not_dvd_num p N n hn hpN x₁.val hx w₁ 1 h1
    rw [one_mul] at this
    exact this h.1
  have ndc : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ c * A₂) := fun h =>
    not_dvd_num p N n hn hpN x₁.val hx w₁ c hc h.1
  rw [sum_perm2 p (N * p ^ n) j hM ζ hζ1 A₁ A₂ 1 (-k₁) (-k₂) h1 r,
    sum_perm2 p (N * p ^ n) j hM ζ hζ1 (c * A₁) (c * A₂) c (-k₁) (-k₂) hc r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj A₁ A₂ nd₁ r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj (c * A₁) (c * A₂) ndc r]
  unfold vp smF
  split_ifs <;> ring

end GlobalTheory.KummerEisensteinGalois.RowFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

theorem ee_add_one (z : ℂ) : ee (z + 1) = ee z := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem rowVectorMulIntMatrixSL2_modularGroupT_apply (x : Fin 2 → ℚ) : act x ModularGroup.T 0 = x 0 ∧ act x ModularGroup.T 1 = x 0 + x 1 := by
  simp [act, ModularGroup.T, Fin.sum_univ_two]

theorem pt_T_smul (x : Fin 2 → ℚ) (τ : ℍ) : pt x (ModularGroup.T • τ) = pt (act x ModularGroup.T) τ := by
  obtain ⟨h0, h1⟩ := rowVectorMulIntMatrixSL2_modularGroupT_apply x
  simp only [pt, coe_T_smul, h0, h1]
  push_cast; ring

theorem sg_T_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  intro c x τ
  simp only [sg]
  rw [pt_T_smul, coe_T_smul, ee_add_one]

end GlobalTheory.Sieg
end

