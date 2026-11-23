module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
section
open GlobalTheory.LGrp Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def upLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → Fin n → ℤ) :
    AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j h =>
    Valuation.map_add_le _ (hX.2 i j h) (hY.2 i j h)⟩
  neg_mem' := fun {X} hX => ⟨fun i j h => by simp [hX.1 i j h], fun i j h => by simpa using hX.2 i j h⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_upLat {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) :=
  Iff.rfl


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mul_mem_upLat {a b c : Fin n → Fin n → ℤ}
    (h : ∀ i j k, i < j → j < k → c i k ≤ a i j + b j k)
    {X Y : Matrix (Fin n) (Fin n) L} (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L a)
    (hY : Y ∈ _root_.GlobalTheory.BorelUMod.upLat L b) : X * Y ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  obtain ⟨hX0, hXv⟩ := hX
  obtain ⟨hY0, hYv⟩ := hY
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hX0 i k hki, zero_mul]
    · rw [hY0 k j (hji.trans hik.le), mul_zero]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · simp [hX0 i k hki]
    rcases le_or_gt j k with hjk | hkj
    · simp [hY0 k j hjk]
    rw [Valuation.map_mul]
    calc Valued.v (X i k) * Valued.v (Y k j)
        ≤ WithZero.exp (-a i k) * WithZero.exp (-b k j) := mul_le_mul' (hXv i k hik) (hYv k j hkj)
      _ = WithZero.exp (-a i k + -b k j) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-c i j) := WithZero.exp_le_exp.2 (by linarith [h i k j hik hkj])

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.upLat_mono {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c :=
  fun _ hX => ⟨hX.1, fun i j hij =>
    (hX.2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (h i j hij)))⟩

def adjJ (σ : L →+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := fun i j => σ (X j.rev i.rev)

def skewJ (σ : L →+* L) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | adjJ σ X = -X}
  zero_mem' := by ext i j; simp [adjJ]
  add_mem' := fun {X Y} hX hY => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hY i) j
    simp only [adjJ, Matrix.neg_apply] at h1 h2
    simp [adjJ, h1, h2, add_comm]
  neg_mem' := fun {X} hX => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    simp only [adjJ, Matrix.neg_apply] at h1
    simp [adjJ, h1]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_skewJ {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mul (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X * Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ Y * _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.mul_apply, map_sum, map_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_add (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X + Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X + _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_sub (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X - Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X - _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_smul (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_one (σ : L →+* L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [_root_.GlobalTheory.BorelUMod.adjJ]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.one_apply, h, h']

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_adjJ {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (_root_.GlobalTheory.BorelUMod.adjJ σ X) = X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ, hσ]


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_GU_iff_adjJ (σ : L →+* L) (g : GL (Fin n) L) :
    g ∈ _root_.Formalism.UG.GU σ n ↔ (g⁻¹).val = _root_.GlobalTheory.BorelUMod.adjJ σ g.val := by
  rw [_root_.GlobalTheory.LGrp.mem_GU_iff]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mem_upLat {σ : L →+* L}
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ}
    (hc : ∀ i j, c j.rev i.rev = c i j) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) :
    _root_.GlobalTheory.BorelUMod.adjJ σ X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · simp [_root_.GlobalTheory.BorelUMod.adjJ, hX.1 j.rev i.rev (Fin.rev_le_rev.2 hji)]
  · simp only [_root_.GlobalTheory.BorelUMod.adjJ]
    rw [hσ, ← hc i j]
    exact hX.2 j.rev i.rev (Fin.rev_lt_rev.2 hij)

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.smul_mem_upLat {c : Fin n → Fin n → ℤ} {a : L}
    (ha : Valued.v a ≤ 1) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) : a • X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => by simp [hX.1 i j hji], fun i j hij => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
  calc Valued.v a * Valued.v (X i j) ≤ 1 * WithZero.exp (-c i j) := mul_le_mul' ha (hX.2 i j hij)
    _ = WithZero.exp (-c i j) := one_mul _

def IsWeight (c : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, c j.rev i.rev = c i j) ∧ ∀ i j k, i < j → j < k → c i k ≤ c i j + c j k

def IsIdealWeight (c C : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, i < j → c i j ≤ C i j) ∧ (∀ i j k, i < j → j < k → C i k ≤ c i j + C j k) ∧
    ∀ i j k, i < j → j < k → C i k ≤ C i j + c j k

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.isWeight_zero :
    _root_.GlobalTheory.BorelUMod.IsWeight (fun _ _ : Fin n => (0 : ℤ)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => by simp⟩

def unipLat {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ} (hc : IsWeight c) :
    Subgroup (borelU σ n).U where
  carrier := {u | (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ upLat L c}
  one_mem' := by
    show ((1 : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L c
    simp
  mul_mem' := fun {u w} hu hw => by
    show u.1.1.val * w.1.1.val - 1 ∈ upLat L c
    have : u.1.1.val * w.1.1.val - 1 = (u.1.1.val - 1) * (w.1.1.val - 1) + (u.1.1.val - 1) + (w.1.1.val - 1) := by
      noncomm_ring
    rw [this]
    exact add_mem (add_mem (mul_mem_upLat hc.2 hu hw) hu) hw
  inv_mem' := fun {u} hu => by
    show (u.1.1⁻¹).val - 1 ∈ upLat L c
    rw [(mem_GU_iff_adjJ σ _).1 u.1.2, ← adjJ_one σ, ← adjJ_sub]
    exact adjJ_mem_upLat hσ hc.1 hu

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_unipLat {σ : L →+* L}
    {hσ : ∀ x, Valued.v (σ x) = Valued.v x} {c : Fin n → Fin n → ℤ}
    {hc : _root_.GlobalTheory.BorelUMod.IsWeight c} {u : (_root_.GlobalTheory.LGrp.borelU σ n).U} :
    u ∈ _root_.GlobalTheory.BorelUMod.unipLat hσ hc ↔
      (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ _root_.GlobalTheory.BorelUMod.upLat L c :=
  Iff.rfl


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.exists_trace_one {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : _root_.Formalism.UG.IsUnramInv ϖ σ q) :
    (∃ θ : L, Valued.v θ ≤ 1 ∧ θ + σ θ = 1) ∧ ∃ d : L, Valued.v d = 1 ∧ σ d = -d := by
  obtain ⟨hinv, -, -, -, ⟨x, hx, hxu⟩, -⟩ := h
  have hx1 : Valued.v x ≤ 1 := hx
  refine ⟨?_, σ x - x, hxu, by rw [map_sub, hinv]; ring⟩
  have h2le : Valued.v (2 : L) ≤ 1 := by
    have h11 : Valued.v ((1 : L) + 1) ≤ 1 :=
      Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_eq (Valuation.map_one _))
    rwa [one_add_one_eq_two] at h11
  rcases h2le.lt_or_eq with h2 | h2
  · have hlt : Valued.v (2 * x) < Valued.v (σ x - x) := by
      rw [hxu, Valuation.map_mul]
      calc Valued.v (2 : L) * Valued.v x ≤ Valued.v (2 : L) * 1 := mul_le_mul' le_rfl hx1
        _ = Valued.v (2 : L) := mul_one _
        _ < 1 := h2
    have ht : Valued.v (x + σ x) = 1 := by
      have e : x + σ x = (σ x - x) + 2 * x := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hlt, hxu]
    have ht0 : x + σ x ≠ 0 := by
      intro e
      rw [e, Valuation.map_zero] at ht
      exact zero_ne_one ht
    refine ⟨x / (x + σ x), ?_, ?_⟩
    · rw [map_div₀, ht, div_one]
      exact hx1
    · rw [map_div₀, map_add (f := _), hinv, add_comm (σ x) x, ← add_div, div_self ht0]
  · refine ⟨1 / 2, ?_, ?_⟩
    · rw [map_div₀, Valuation.map_one, h2, div_one]
    · rw [map_div₀, map_one, map_ofNat]
      have h20 : (2 : L) ≠ 0 := by
        intro e
        rw [e, Valuation.map_zero] at h2
        exact zero_ne_one h2
      rw [← add_div, one_add_one_eq_two, div_self h20]

end GlobalTheory.BorelUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (w : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : b < a then w ⟨(a, b), h⟩ else if a = b then 1 else 0

def colGram {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (k : Fin (q + 1)) : ℝ := ‖lminor (Mᴴ * M) k‖

def blkW {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℂ := fun i j =>
  if p0 = 1 then lowMat w ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ else lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩

def gB {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : ℝ :=
  ∏ k : Fin (r - 1), colGram (blkW p0 w) k.castSucc ^ (-2 : ℤ)

def hB {r : ℕ} (p0 : ℕ) : (Low r → ℂ) → ℝ≥0∞ :=
  Set.indicator {w | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    fun w => ENNReal.ofReal (gB p0 w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zOf (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Low r → ℂ := fun p =>
  z (Fintype.equivFin (Ent X) ⟨τ, p⟩)

def bnd (X : Data E r) (z : V (nd X)) : ℝ := ∏ τ, gB X.p0 (zOf X z τ)

theorem nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]

end

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCharacterUnitEqOneHeisenberg
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_mem_integer_iff_of_valuation_eq_one {u : kˣ} (hu : valuation k (u : k) = 1) (y : k) :
    (u : k) * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]

theorem intInd_diagAt_mul {n d : ℕ} {u : kˣ} (hu : valuation k (u : k) = 1) (i0 : Fin n)
    (Y : Matrix (Fin n) (Fin d) k) : intInd (k := k) n d ((diagAt u i0).valᵀ * Y) = intInd (k := k) n d Y := by
  have e : ∀ i j, ((diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
    by_cases hi : i = i0
    · rw [if_pos hi]; exact mul_mem_integer_iff_of_valuation_eq_one hu _
    · rw [if_neg hi, one_mul]
  have hs : ((diagAt u i0).valᵀ * Y) ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} ↔
      Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := by
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => e i j
  unfold intInd
  by_cases h : Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hs.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hs.mp h)]

theorem norm_char_unit_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  set g := diagAt u i0 with hg
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, det_diagAt]
    funext Y
    rw [intInd_diagAt_mul hu i0 Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) := inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2

end GlobalTheory.HeisUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isLocalization_away_of_eq_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (V : X.Opens) (hV : V = X.basicOpen g) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra;
    IsLocalization.Away g Γ(X, V) := by
  subst hV
  exact hU.isLocalization_basicOpen g

theorem famIdeal_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  intro Y Z π _ _ _ hK hfd I U f hU
  by_cases hD : genPt π ∈ Z.basicOpen f
  · have hζU : genPt π ∈ U.1 := Z.basicOpen_le f hD
    have hD' : genPt π ∈ (Z.affineBasicOpen f).1 := hD
    have hUD : ((Z.affineBasicOpen f : Z.affineOpens) : Set Z) ⊆ Set.range π :=
      fun x hx => hU (Z.basicOpen_le f hx)
    letI := fieldK π hK
    letI := algKL π
    obtain ⟨hdomA, hfrA⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hU hζU
    obtain ⟨_, hfrA'⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π (Z.basicOpen f) (Z.affineBasicOpen f).2 hUD hD
    letI iA := algAK π U.1 hζU
    letI iB := algBL π U.1 hζU
    letI iA' := algAK π (Z.basicOpen f) hD
    letI iB' := algBL π (Z.basicOpen f) hD
    letI iAA' : Algebra Γ(Z, U) Γ(Z, Z.basicOpen f) :=
      (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
    have hleY : π ⁻¹ᵁ Z.basicOpen f ≤ π ⁻¹ᵁ U.1 := π.preimage_mono (Z.basicOpen_le f)
    letI iBB' : Algebra Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      (Y.presheaf.map (homOfLE hleY).op).hom.toAlgebra
    letI iAB : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) := U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      isLocalization_away_of_eq_basicOpen (U.2.preimage π) (π.app U.1 f) _
        (Scheme.preimage_basicOpen π f) hleY
    have h1 : (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))).comp
        (algebraMap Γ(Z, U) Γ(Z, Z.basicOpen f)) = algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)) := by
      ext a
      exact Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le f)) (genPt π) hD a
    have h2 : (algebraMap Γ(Y, π ⁻¹ᵁ Z.basicOpen f) Y.functionField).comp
        (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) =
          algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField := by
      ext a
      exact Y.presheaf.germ_res_apply (homOfLE hleY) (genericPoint Y) hD a
    have h3 : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
        (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))) =
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField).comp (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1)) := by
      ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) hζU a
    have h4 : Function.Injective (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))) :=
      IsFractionRing.injective _ _
    have h5 : ∀ {m : ℕ} (g : Fin m → Γ(Y, π ⁻¹ᵁ U.1)) s,
        (GlobalTheory.NormSheaf.normForm (Z.presheaf.stalk (genPt π)) Y.functionField
          (fun i => algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField (g i))).coeff s ∈
            (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))).range := by
      intro m g s
      haveI : IsIntegrallyClosed Γ(Z, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2
      letI iAL : Algebra Γ(Z, U) Y.functionField :=
        ((algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
          (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)))).toAlgebra
      haveI : IsScalarTower Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hfin : (π.app U.1).hom.Finite := π.finite_app U.1 U.2
      let φ : Γ(Y, π ⁻¹ᵁ U.1) →ₐ[Γ(Z, U)] Y.functionField :=
        { algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField with
          commutes' := fun a => (congrArg (fun h => h a) h3).symm }
      refine _root_.GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField _ (fun i => ?_) s
      have hi : IsIntegral Γ(Z, U) (g i) := hfin.to_isIntegral (g i)
      exact hi.map φ
    have hJ : I.ideal ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩ =
        (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) :=
      (I.map_ideal (U := ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩)
        (V := ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) hleY).symm
    simp only [famIdeal, dif_pos hζU, dif_pos hD']
    rw [hJ]
    exact _root_.GlobalTheory.NormSheaf.normIdeal_map_away Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      Γ(Z, Z.basicOpen f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) f h1 h2 h3 h4 h5 _
  · have hbot : Z.basicOpen f = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨y, rfl⟩ := hU (Z.basicOpen_le f hx)
      exact hD (((genericPoint_specializes y).map π.continuous).mem_open (Z.basicOpen f).isOpen hx)
    haveI : Subsingleton Γ(Z, Z.basicOpen f) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    haveI : Subsingleton Γ(Z, (Z.affineBasicOpen f : Z.Opens)) := this
    ext x
    rw [Subsingleton.elim x 0]
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealUniquePrimeOver
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
end

