module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.ParahoricConjBlocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (z : k) :
    valuation k z < 1 ↔ valuation k z ≤ valuation k (ϖ : k) := by
  rw [hϖ, le_uniformizer_iff]

theorem scal₁ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y ≤ 1 ∧ valuation k (y * (ϖ : k) ^ n) ≤ 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ max 0 (-n)) := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, ← le_mul_inv_iff₀ (zpow_pos h0 n), one_mul, ← _root_.zpow_neg]
  rcases le_total 0 n with hn | hn
  · rw [max_eq_left (by omega), zpow_zero]
    have : (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) ^ (-n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show -n ≤ 0 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩
  · rw [max_eq_right (by omega)]
    have : valuation k (ϖ : k) ^ (-n) ≤ 1 := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 0 ≤ -n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩

theorem scal₂ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y < 1 ∧ valuation k ((ϖ : k) ^ (-n) * y) < 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ (1 + max 0 n)) := by
  rw [val_lt_one_iff hϖ, val_lt_one_iff hϖ]
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, mul_comm (valuation k (ϖ : k) ^ (-n)),
    ← le_mul_inv_iff₀ (zpow_pos h0 _), ← _root_.zpow_neg, neg_neg, ← zpow_one_add₀ h0.ne']
  rcases le_total 0 n with hn | hn
  · rw [max_eq_right hn]
    have : valuation k (ϖ : k) ^ (1 + n) ≤ valuation k (ϖ : k) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 ≤ 1 + n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩
  · rw [max_eq_left hn, add_zero, zpow_one]
    have : valuation k (ϖ : k) ≤ valuation k (ϖ : k) ^ (1 + n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 + n ≤ 1 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩

theorem isUnit_det_iff_of_lower {R : Type} [CommRing R] [IsLocalRing R] {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (N : Matrix (A ⊕ D) (A ⊕ D) R)
    (hN : ∀ i j, N (.inr i) (.inl j) ∈ IsLocalRing.maximalIdeal R) :
    IsUnit N.det ↔ IsUnit N.toBlocks₁₁.det ∧ IsUnit N.toBlocks₂₂.det := by
  simp only [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply]
  have e : N.map (IsLocalRing.residue R) = fromBlocks (N.toBlocks₁₁.map (IsLocalRing.residue R))
      (N.toBlocks₁₂.map (IsLocalRing.residue R)) 0 (N.toBlocks₂₂.map (IsLocalRing.residue R)) := by
    ext (i | i) (j | j) <;> simp [IsLocalRing.residue_eq_zero_iff, hN, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
  rw [e, det_fromBlocks_zero₂₁, mul_ne_zero_iff]

theorem mem_KO_val_iff {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n k) :
    y ∈ Units.val '' (KO k n : Set (GL n k)) ↔ (∀ i j, valuation k (y i j) ≤ 1) ∧ valuation k y.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  constructor
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    refine ⟨fun i j => (u.val i j).2, ?_⟩
    show valuation k ((algebraMap 𝒪[k] k).mapMatrix u.val).det = 1
    rw [← RingHom.map_det, ← hI.isUnit_iff_valuation_eq_one]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  · rintro ⟨h1, h2⟩
    let N : Matrix n n 𝒪[k] := fun i j => ⟨y i j, h1 i j⟩
    have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
    have hu : IsUnit N := by
      rw [Matrix.isUnit_iff_isUnit_det, hI.isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
      exact h2
    exact ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit, ⟨hu.unit, rfl⟩, hN⟩

theorem val_det_iff_of_lower {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) (hi : ∀ i j, valuation k (y i j) ≤ 1)
    (hl : ∀ i j, valuation k (y (.inr i) (.inl j)) < 1) :
    valuation k y.det = 1 ↔ valuation k y.toBlocks₁₁.det = 1 ∧ valuation k y.toBlocks₂₂.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  let N : Matrix (A ⊕ D) (A ⊕ D) 𝒪[k] := fun i j => ⟨y i j, hi i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
  have h11 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₁₁ = y.toBlocks₁₁ := by ext; rfl
  have h22 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₂₂ = y.toBlocks₂₂ := by ext; rfl
  have key := isUnit_det_iff_of_lower N (fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact (hl i j).ne)
  rwa [hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one,
    RingHom.map_det, RingHom.map_det, RingHom.map_det, hN, h11, h22] at key

theorem mem_parahoric_val_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) :
    y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧ (∀ i j, valuation k (y.toBlocks₁₂ i j) ≤ 1) ∧
      (∀ i j, valuation k (y.toBlocks₂₁ i j) < 1) ∧ y.toBlocks₂₂ ∈ Units.val '' (KO k D : Set (GL D k)) := by
  have step : y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y ∈ Units.val '' (KO k (A ⊕ D) : Set (GL (A ⊕ D) k)) ∧ ∀ i j, valuation k (y (.inr i) (.inl j)) < 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (mem_parahoric.1 hg).1, rfl⟩, (mem_parahoric.1 hg).2⟩
    · rintro ⟨⟨g, hg, rfl⟩, h⟩
      exact ⟨g, mem_parahoric.2 ⟨hg, h⟩, rfl⟩
  rw [step, mem_KO_val_iff, mem_KO_val_iff, mem_KO_val_iff]
  constructor
  · rintro ⟨⟨hi, hd⟩, hl⟩
    have hd' := (val_det_iff_of_lower y hi hl).1 hd
    exact ⟨⟨fun i j => hi _ _, hd'.1⟩, fun i j => hi _ _, hl, ⟨fun i j => hi _ _, hd'.2⟩⟩
  · rintro ⟨⟨h11, d11⟩, h12, hl, ⟨h22, d22⟩⟩
    have hi : ∀ i j, valuation k (y i j) ≤ 1 := by
      rintro (i | i) (j | j)
      · exact h11 i j
      · exact h12 i j
      · exact (hl i j).le
      · exact h22 i j
    exact ⟨⟨hi, (val_det_iff_of_lower y hi hl).2 ⟨d11, d22⟩⟩, hl⟩

theorem mem_val_map_conj_inf {n : Type} [Fintype n] [DecidableEq n] (K : Subgroup (GL n k)) (t : GL n k)
    (y : Matrix n n k) :
    y ∈ Units.val '' ((K.map (MulAut.conj t).toMonoidHom ⊓ K : Subgroup (GL n k)) : Set (GL n k)) ↔
      y ∈ Units.val '' (K : Set (GL n k)) ∧
        (t⁻¹ : GL n k).val * y * t.val ∈ Units.val '' (K : Set (GL n k)) := by
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
    replace hg1 : g ∈ K.map (MulAut.conj t).toMonoidHom := hg1
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hg1
    exact ⟨⟨g, hg2, rfl⟩, ⟨_, hg1, by simp⟩⟩
  · rintro ⟨⟨g, hg, rfl⟩, ⟨h, hh, e⟩⟩
    refine ⟨g, ⟨?_, hg⟩, rfl⟩
    show g ∈ K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have : t⁻¹ * g * t = h := Units.ext (by simp [e])
    rwa [this]

theorem val_inv_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (f : n → ℤ) :
    ((torusElt k n ϖ f)⁻¹).val = diagonal fun i => (ϖ : k) ^ (-f i) := by
  have : (torusElt k n ϖ f)⁻¹ = torusElt k n ϖ (-f) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simpa only [Pi.mul_apply, Pi.neg_apply, Pi.one_apply, _root_.zpow_neg] using
      inv_mul_cancel₀ (zpow_ne_zero (f i) ϖ.ne_zero)
  rw [this, val_torusElt]
  rfl

section conjBlocks
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ)
  (x : Matrix (A ⊕ D) (A ⊕ D) k)

theorem conj_apply (i j : A ⊕ D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)) i j =
      (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) * x i j * (ϖ : k) ^ (Sum.elim 0 e j : ℤ) := by
  have h1 : ((mtor (A := A) ϖ e)⁻¹.val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) := val_inv_torusElt _ _
  have h2 : ((mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (Sum.elim 0 e i : ℤ) := val_torusElt _ _
  rw [h1, h2, mul_diagonal, diagonal_mul]

theorem conj_toBlocks₁₁ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ =
      x.toBlocks₁₁ := by
  ext i j
  simp only [toBlocks₁₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₁₂ (i : A) (j : D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₂ i j =
      x.toBlocks₁₂ i j * (ϖ : k) ^ e j := by
  simp only [toBlocks₁₂, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₁ (i : D) (j : A) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₁ i j =
      (ϖ : k) ^ (-e i) * x.toBlocks₂₁ i j := by
  simp only [toBlocks₂₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₂ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₂ =
      ((torusElt k D ϖ e)⁻¹.val * x.toBlocks₂₂ * (torusElt k D ϖ e).val : Matrix D D k) := by
  have h1 : ((torusElt k D ϖ e)⁻¹.val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ (-e i) := val_inv_torusElt _ _
  have h2 : ((torusElt k D ϖ e).val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ e i := val_torusElt _ _
  rw [h1, h2]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [toBlocks₂₂, of_apply]
  rw [conj_apply]
  simp

end conjBlocks

theorem blockset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  intro k _ _ _ _ ϖ hϖ A D _ _ _ _ e
  ext x
  rw [mem_val_map_conj_inf, mem_parahoric_val_iff, mem_parahoric_val_iff, conj_toBlocks₁₁, conj_toBlocks₂₂]
  simp only [conj_toBlocks₁₂, conj_toBlocks₂₁, Set.mem_setOf_eq, mem_val_map_conj_inf, ← scal₁ hϖ, ← scal₂ hϖ,
    forall_and]
  tauto

end GlobalTheory.ParahoricConjBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

section Pow
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}

theorem val_pos (x : kˣ) : 0 < valuation k (x : k) := by simp [zero_lt_iff]

theorem mem_pow {e : ℤ} {s : k} : s ∈ powInt ϖ e ↔ valuation k s ≤ valuation k (ϖ : k) ^ e := by
  simp [powInt]

theorem mem_pow_zero {s : k} : s ∈ powInt ϖ 0 ↔ s ∈ 𝒪[k] := by
  rw [mem_pow, zpow_zero]; rfl

theorem zpow_mul_mem_pow {a b : ℤ} {s : k} : (ϖ : k) ^ a * s ∈ powInt ϖ b ↔ s ∈ powInt ϖ (b - a) := by
  have h := val_pos ϖ
  rw [mem_pow, mem_pow, map_mul, map_zpow₀, zpow_sub₀ h.ne', le_div_iff₀ (zpow_pos h a), mul_comm]

theorem zero_mem_pow {e : ℤ} : (0 : k) ∈ powInt ϖ e := by simp [mem_pow]

theorem pow_mul_pow {a b : ℤ} {t s : k} (ht : t ∈ powInt ϖ a) (hs : s ∈ powInt ϖ b) : t * s ∈ powInt ϖ (a + b) := by
  rw [mem_pow] at ht hs ⊢
  rw [map_mul, zpow_add₀ (val_pos ϖ).ne']
  exact mul_le_mul' ht hs

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ

theorem zpow_mem_pow {a b : ℤ} : (ϖ : k) ^ a ∈ powInt ϖ b ↔ b ≤ a := by
  rw [mem_pow, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ (val_pos ϖ) (hϖ ▸ uniformizer_lt_one)]

theorem pow_mono {a b : ℤ} (h : a ≤ b) {s : k} (hs : s ∈ powInt ϖ b) : s ∈ powInt ϖ a := by
  have := (zpow_mem_pow hϖ).2 h
  rw [mem_pow] at hs this ⊢
  rw [map_zpow₀] at this
  exact hs.trans this

end Pow

section Lat
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_latOf_mul {g a : GL Y k} {y : Y → k} : y ∈ latOf (g * a) ↔ (g⁻¹).val *ᵥ y ∈ latOf a := by
  simp [mem_latOf, mulVec_mulVec]

theorem latOf_mul_congr (g : GL Y k) {a b : GL Y k} (h : latOf a = latOf b) : latOf (g * a) = latOf (g * b) := by
  ext y; rw [mem_latOf_mul, mem_latOf_mul, h]

omit [Fintype Y] [DecidableEq Y] in
theorem smul_mem_lat {L : Submodule 𝒪[k] (Y → k)} {t : k} (ht : t ∈ 𝒪[k]) {y : Y → k} (hy : y ∈ L) : t • y ∈ L :=
  L.smul_mem ⟨t, ht⟩ hy

theorem mapsLat_iff {x : Matrix Y Y' k} {g : GL Y' k} {h : GL Y k} :
    MapsLat x (latOf g) (latOf h) ↔ IntM ((h⁻¹).val * x * g.val) := by
  constructor
  · intro H i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := H _ this i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro H y hy i
    have : (h⁻¹).val *ᵥ (x *ᵥ y) = ((h⁻¹).val * x * g.val) *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (H i l) (hy l)

theorem mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (nfBasis ϖ g e z) ↔
      (fun r => y (.inl r) - y (.inr 0) * z r) ∈ latOf g ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  have key : (nfBasis ϖ g e z).val *ᵥ Sum.elim ((g⁻¹).val *ᵥ fun r => y (.inl r) - y (.inr 0) * z r)
      (fun i => (ϖ : k) ^ (-e i) * y (.inr i)) = y := by
    have h0 : ∀ a : ℤ, (ϖ : k) ^ a ≠ 0 := fun a => zpow_ne_zero _ ϖ.ne_zero
    rw [nfBasis_val, fromBlocks_mulVec]
    ext (r | i)
    · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, Units.mul_inv, one_mulVec,
        Pi.add_apply]
      simp [mulVec, dotProduct]
      field_simp
      ring
    · simp [mulVec_diagonal, h0]
  conv_lhs => rw [← key, ← mul_one (nfBasis ϖ g e z)]
  rw [mul_one, ← mul_one (nfBasis ϖ g e z)]
  conv_lhs => enter [2]; rw [mul_one]
  rw [mulVec_mem_latOf, mem_latOf_one, Sum.forall]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [Sum.elim_inr, ← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]; simp

theorem mem_normal {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (normalBasis ϖ e z) ↔
      (∀ r, y (.inl r) - y (.inr 0) * z r ∈ 𝒪[k]) ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  rw [← nfBasis_one, mem_nf, mem_latOf_one]

omit [ValuativeRel k] in
theorem N_mulVec {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (y : n ⊕ Fin c → k) (r : n ⊕ Fin c)
    (h : ∀ s, lev p r < lev p s → y s = 0) : (u.val *ᵥ y) r = y r := by
  have hu' := (Radical.mem_N_iff u).1 hu
  conv_rhs => rw [← one_mulVec y]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases le_or_gt (lev p s) (lev p r) with hs | hs
  · exact congrArg (· * y s) (hu' r s hs)
  · simp [h s hs]


omit [ValuativeRel k] in
theorem N_fix {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (y : n ⊕ Fin c → k)
    (h : ∀ l : Fin c, 0 < l.val → y (.inr l) = 0) : u.val *ᵥ y = y := by
  ext r
  refine N_mulVec hu y r ?_
  rintro (s | s) hs
  · rcases r with r | r <;> simp [lev] at hs
  · apply h
    rcases r with r | r <;> simp [lev] at hs <;> omega

omit [ValuativeRel k] in
theorem embX_mulVec (x : GL n k) (y : n ⊕ Fin c → k) :
    (embX c x).val *ᵥ y = Sum.elim (x.val *ᵥ fun r => y (.inl r)) fun l => y (.inr l) := by
  rw [Radical.embX_val, fromBlocks_mulVec]; simp; rfl

theorem topCoord_le {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf h) i ⊆ topCoord (latOf (r * h)) i := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  rintro _ ⟨y, hy, h0, rfl⟩
  have key : ∀ l, i ≤ l → ((embX c x * u).val *ᵥ y) (.inr l) = y (.inr l) := fun l hl => by
    rw [Units.val_mul, ← mulVec_mulVec, embX_mulVec, Sum.elim_inr]
    refine N_mulVec hu y _ ?_
    rintro (s | s) hs
    · simp [lev] at hs
    · apply h0
      simp [lev] at hs
      exact lt_of_le_of_lt hl hs
  exact ⟨_, (mulVec_mem_latOf _).2 hy, fun l hl => (key l hl.le).trans (h0 l hl), key i le_rfl⟩

theorem topCoord_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf (r * h)) i = topCoord (latOf h) i := by
  refine Set.Subset.antisymm ?_ (topCoord_le hr h i)
  have := topCoord_le (inv_mem hr) (r * h) i
  rwa [inv_mul_cancel_left] at this

theorem col_mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} (i : Fin (c + 1)) {s : k}
    (hs : s ∈ powInt ϖ (e i)) :
    (Sum.elim (fun r => if i = 0 then s * z r else 0) (Pi.single i s) : n ⊕ Fin (c + 1) → k) ∈
      latOf (nfBasis ϖ g e z) := by
  refine mem_nf.2 ⟨?_, fun l => ?_⟩
  · convert zero_mem (latOf g) using 1
    ext r
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  · rw [Sum.elim_inr, Pi.single_apply]
    split_ifs with h
    · rwa [h]
    · exact zero_mem_pow

theorem topCoord_nf (g : GL n k) (e : Fin (c + 1) → ℤ) (z : n → k) (i : Fin (c + 1)) :
    topCoord (latOf (nfBasis ϖ g e z)) i = powInt ϖ (e i) := by
  ext s
  constructor
  · rintro ⟨y, hy, -, rfl⟩
    exact (mem_nf.1 hy).2 i
  · intro hs
    exact ⟨_, col_mem_nf i hs, fun l hl => by simp [hl.ne'], by simp⟩

omit [ValuativeRel k] in
theorem embX_mul_nf (x g : GL n k) (e : Fin c → ℤ) (z : n → k) :
    embX c x * nfBasis ϖ g e z = nfBasis ϖ (x * g) e (x.val *ᵥ z) := by
  ext1
  rw [Units.val_mul, nfBasis_val, nfBasis_val, Radical.embX_val, fromBlocks_multiply]
  ext (r | r) (s | s)
  · simp
  · by_cases h : s.val = 0 <;> simp [h, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  · simp
  · simp

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latOf_eq_of_KO {g : GL Y k} (hg : g ∈ KO k Y) : latOf g = latOf 1 := by
  have := (mem_stabLat_iff (g := 1) (h := g)).1 (by simpa [mem_stabLat] using hg)
  rwa [mul_one] at this

theorem om_supp {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ} (hs : ∀ x, Φ x ≠ 0 → IntM x) (g : GL Y' k) (h : GL Y k)
    (x : Matrix Y Y' k) (hx : om μ g h Φ x ≠ 0) : MapsLat x (latOf g) (latOf h) :=
  mapsLat_iff.2 (hs _ (right_ne_zero_of_mul hx))

theorem om_per (hϖ : valuation k (ϖ : k) = uniformizer k) {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ}
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) (g : GL Y' k) (h : GL Y k)
    (x y : Matrix Y Y' k) (hy : MapsLat y (latOf g) (latOf h)) :
    om μ g h Φ (x + (ϖ : k) • y) = om μ g h Φ x := by
  unfold om
  rw [Matrix.mul_add, Matrix.add_mul, hp]
  intro i j
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hϖ]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le uniformizer_lt_one (mapsLat_iff.1 hy i j)

end Lat

end GlobalTheory.LatClass
end

