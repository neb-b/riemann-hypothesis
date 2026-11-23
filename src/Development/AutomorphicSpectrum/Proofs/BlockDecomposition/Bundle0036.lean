module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0009
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriBlockUpperLeviLower
section
open Matrix

namespace GlobalTheory.CompanionTheory.BlockIwahoriUML

variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

def Cong (v : Valuation k Γ) (r : Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, v (A i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r

theorem exists_udl (v : Valuation k Γ) {r : Γ} (hr : r < 1) (n : ℕ)
    (g : Matrix (Fin n) (Fin n) k) (hg : Cong v r g) :
    ∃ u d l : Matrix (Fin n) (Fin n) k, Cong v r u ∧ Cong v r l ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  classical
  let I : Ideal v.integer :=
    { carrier := {x | v (x : k) ≤ r}
      add_mem' := fun {a b} ha hb => by
        have := Valuation.map_add_le v ha hb
        simpa using this
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hc : v (c : k) ≤ 1 := c.2
        have hx' : v (x : k) ≤ r := hx
        show v ((c * x : v.integer) : k) ≤ r
        rw [Subring.coe_mul, map_mul]
        calc v (c : k) * v (x : k) ≤ 1 * r := mul_le_mul' hc hx'
          _ = r := one_mul r }
  have hImem : ∀ x : v.integer, x ∈ I ↔ v (x : k) ≤ r := fun x => Iff.rfl
  have hI : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    have hx' : v (x : k) < 1 := lt_of_le_of_lt ((hImem x).1 hx) hr
    have h1 : v (1 + (x : k)) = 1 := Valuation.map_one_add_of_lt v hx'
    have h0 : (1 + (x : k)) ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (1 + (x : k))⁻¹ ∈ v.integer := by
      show v _ ≤ 1
      rw [map_inv₀, h1, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨(1 + (x : k))⁻¹, hmem⟩, Subtype.ext ?_⟩
    simpa using mul_inv_cancel₀ h0
  have hone : ∀ i j, v ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ i j, v (g i j) ≤ 1 := by
    intro i j
    have := Valuation.map_add_le v ((hg i j).trans hr.le) (hone i j)
    simpa using this
  let g' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨g i j, hint i j⟩
  have hone' : ∀ i j, (((1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : k) =
      (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg' : ∀ i j, g' i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I := by
    intro i j
    rw [hImem, AddSubgroupClass.coe_sub, hone']
    exact hg i j
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := IwahoriUDL.exists_udl_of_isUnit I hI n g' hg'
  have back : ∀ a : Matrix (Fin n) (Fin n) v.integer,
      (∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I) →
        Cong v r (a.map v.integer.subtype) := by
    intro a ha i j
    have := (hImem _).1 (ha i j)
    rw [AddSubgroupClass.coe_sub, hone'] at this
    exact this
  refine ⟨u.map v.integer.subtype, d.map v.integer.subtype, l.map v.integer.subtype,
    back u hu.1, back l hl.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hu.2.1 i j hij]
  · intro i
    simp [hu.2.2 i]
  · intro i j hij
    simp [hd.2 i j hij]
  · intro i j hij
    simp [hl.2.1 i j hij]
  · intro i
    simp [hl.2.2 i]
  · have hgg : g = g'.map v.integer.subtype := by
      ext i j
      rfl
    rw [hgg, h, Matrix.map_mul, Matrix.map_mul]

theorem up_split (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (u : Matrix (Fin n) (Fin n) k) (hu : Cong v r u)
    (hu0 : ∀ i j, j < i → u i j = 0) (hu1 : ∀ i, u i i = 1) :
    ∃ a m : Matrix (Fin n) (Fin n) k, a.det = 1 ∧ m.det = 1 ∧ Cong v r a ∧ Cong v r m ∧
      (∀ i j, β j ≤ β i → a i j = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → m i j = 0) ∧ u = a * m := by
  classical
  let m : Matrix (Fin n) (Fin n) k := fun i j => if β i = β j then u i j else 0
  have hmb : ∀ i j, β i ≠ β j → m i j = 0 := fun i j h => if_neg h
  have hmu : ∀ i j, β i = β j → m i j = u i j := fun i j h => if_pos h
  have hm0 : ∀ i j, j < i → m i j = 0 := by
    intro i j h
    by_cases hb : β i = β j
    · rw [hmu i j hb, hu0 i j h]
    · exact hmb i j hb
  have hm1 : ∀ i, m i i = 1 := fun i => by rw [hmu i i rfl, hu1]
  have hdet : ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, j < i → A i j = 0) → (∀ i, A i i = 1) →
      A.det = 1 := by
    intro A h0 h1
    rw [Matrix.det_of_upperTriangular (fun i j h => h0 i j h)]
    simp [h1]
  have hmd : m.det = 1 := hdet m hm0 hm1
  have hud : u.det = 1 := hdet u hu0 hu1
  have hmC : Cong v r m := by
    intro i j
    by_cases hb : β i = β j
    · rw [hmu i j hb]
      exact hu i j
    · have hij : i ≠ j := fun e => hb (by rw [e])
      rw [hmb i j hb, Matrix.one_apply_ne hij]
      simp
  have hmU : IsUnit m.det := by simp [hmd]
  have huU : IsUnit u.det := by simp [hud]
  haveI : Invertible m := Matrix.invertibleOfIsUnitDet m hmU
  have hmw : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hmU
  have hwm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hmU
  have hbu : BlockTriangular u β := by
    intro i j h
    refine hu0 i j ?_
    by_contra hc
    exact absurd (hβ (not_lt.1 hc)) (not_le.2 h)
  have hbm : BlockTriangular m β := fun i j h => hmb i j h.ne'
  have hbw : BlockTriangular m⁻¹ β := Matrix.blockTriangular_inv_of_blockTriangular hbm
  have hK : Cong v r (u * m⁻¹) := by
    let ug : GL (Fin n) k := Matrix.nonsingInvUnit u huU
    let mg : GL (Fin n) k := Matrix.nonsingInvUnit m hmU
    have hugK : ug ∈ PrincipalCongruence.principalCongruence v r hr := hu
    have hmgK : mg ∈ PrincipalCongruence.principalCongruence v r hr := hmC
    have hag := mul_mem hugK (inv_mem hmgK)
    have hcoe : ((ug * mg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = u * m⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv]
      rfl
    intro i j
    have := hag i j
    rwa [hcoe] at this
  refine ⟨u * m⁻¹, m, ?_, hmd, hK, hmC, ?_, hmb, ?_⟩
  · rw [Matrix.det_mul, hud, Matrix.det_nonsing_inv, hmd]
    simp
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · have hne : i ≠ j := fun e => h.ne (by rw [e])
      rw [Matrix.one_apply_ne hne]
      exact (hbu.mul hbw) h
    · have key : (u * m⁻¹) i j = (m * m⁻¹) i j := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases lt_trichotomy (β x) (β i) with hx | hx | hx
        · rw [hbu hx, hbm hx]
        · rw [hmu i x hx.symm]
        · have : m⁻¹ x j = 0 := hbw (by rw [h]; exact hx)
          rw [this, mul_zero, mul_zero]
      rw [key, hmw]
  · rw [Matrix.mul_assoc, hwm, Matrix.mul_one]

theorem cong_transpose (v : Valuation k Γ) {r : Γ} {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (hA : Cong v r A) : Cong v r Aᵀ := by
  intro i j
  have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) j i := by
    simp [Matrix.one_apply, eq_comm]
  rw [h1, Matrix.transpose_apply]
  exact hA j i

theorem units_conj {M : Type*} [Monoid M] (p q : Mˣ) (x : M) :
    ((p⁻¹ : Mˣ) : M) * ((p : M) * x * (q : M)) * ((q⁻¹ : Mˣ) : M) = x := by
  simp [mul_assoc]

theorem blockDiag_mul {n : ℕ} (β : Fin n → ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) (hB : ∀ i j, β i ≠ β j → B i j = 0) :
    ∀ i j, β i ≠ β j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : β i = β x
  · rw [hB x j (fun e => hij (hx.trans e)), mul_zero]
  · rw [hA i x hx, zero_mul]

theorem factor (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (g : GL (Fin n) k) (hg : Cong v r (g : Matrix (Fin n) (Fin n) k)) :
    ∃ nm : GL (Fin n) k, Cong v r (nm : Matrix (Fin n) (Fin n) k) ∧
    ∃ l : GL (Fin n) k, Cong v r (l : Matrix (Fin n) (Fin n) k) ∧
    ∃ np : GL (Fin n) k, Cong v r (np : Matrix (Fin n) (Fin n) k) ∧
      (∀ i j, β i ≤ β j → (nm : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → (l : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      (∀ i j, β j ≤ β i → (np : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧ g = np * l * nm := by
  classical
  obtain ⟨u, d, t, hu, ht, hu0, hu1, hd0, ht0, ht1, hudt⟩ := exists_udl v hr n _ hg
  obtain ⟨a, m, had, hmd, haC, hmC, hab, hmb, huam⟩ := up_split v hr β hβ u hu hu0 hu1
  have htC : Cong v r tᵀ := cong_transpose v ht
  obtain ⟨b, c, hbd, hcd, hbC, hcC, hbb, hcb, htbc⟩ :=
    up_split v hr β hβ tᵀ htC (fun i j h => ht0 j i h) ht1
  have htt : t = cᵀ * bᵀ := by
    rw [← Matrix.transpose_mul, ← htbc, Matrix.transpose_transpose]
  have hbtC : Cong v r bᵀ := cong_transpose v hbC
  let npg : GL (Fin n) k := Matrix.nonsingInvUnit a (by simp [had])
  let nmg : GL (Fin n) k := Matrix.nonsingInvUnit bᵀ (by simp [hbd])
  have hnpK : npg ∈ PrincipalCongruence.principalCongruence v r hr := haC
  have hnmK : nmg ∈ PrincipalCongruence.principalCongruence v r hr := hbtC
  have hgK : g ∈ PrincipalCongruence.principalCongruence v r hr := hg
  have hlK := mul_mem (mul_mem (inv_mem hnpK) hgK) (inv_mem hnmK)
  have hprod : (g : Matrix (Fin n) (Fin n) k) =
      (npg : Matrix (Fin n) (Fin n) k) * (m * d * cᵀ) * (nmg : Matrix (Fin n) (Fin n) k) := by
    show (g : Matrix (Fin n) (Fin n) k) = a * (m * d * cᵀ) * bᵀ
    rw [hudt, huam, htt]
    simp only [Matrix.mul_assoc]
  have hlev : ((npg⁻¹ * g * nmg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = m * d * cᵀ := by
    rw [Units.val_mul, Units.val_mul, hprod]
    exact units_conj npg nmg _
  refine ⟨nmg, hnmK, npg⁻¹ * g * nmg⁻¹, hlK, npg, hnpK, ?_, ?_, hab, by group⟩
  · intro i j hij
    show bᵀ i j = _
    rw [Matrix.transpose_apply, hbb j i hij, ← Matrix.transpose_apply (1 : Matrix (Fin n) (Fin n) k) j i, Matrix.transpose_one]
  · rw [hlev]
    refine blockDiag_mul β (blockDiag_mul β hmb ?_) ?_
    · intro i j hij
      exact hd0 i j (fun e => hij (by rw [e]))
    · intro i j hij
      exact hcb j i hij.symm

theorem iwahori_block_upper_levi_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (β : Fin N → ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Monotone β → ∀ g ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ nm ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ l ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ np ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, (∀ i j, β i ≤ β j → (nm : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ (∀ i j, β i ≠ β j → (l : Matrix (Fin N) (Fin N) k) i j = 0) ∧ (∀ i j, β j ≤ β i → (np : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ g = np * l * nm := by
  intro k _ _ _ _ N ϖ m β _ hϖ _ hm hβ g hg
  have hr : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hϖ (by omega)
  exact factor (ValuativeRel.valuation k) hr β hβ g hg

end GlobalTheory.CompanionTheory.BlockIwahoriUML
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
section
noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))

def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)

def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2

def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
section
noncomputable section

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

def sumG {k : Type} [Field k] {n : ℕ} (f : GL (Ix n) k → ℂ) : ℂ := ∑ᶠ g, f g

def JpIw : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (g : GL (Ix n) L), ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
      g = pM a d b * inL κ

def JpHgt : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h → ∀ κ : GL (Ix n) O,
      h (inL κ * (tauM w)⁻¹) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ)) /
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ n

def JpUnif : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O),
    Irreducible ϖ → ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
    MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ φ : GL (Ix n) O → ℂ,
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∫ x, φ (ρ x) ∂ν = avgK ϖ φ

def JpCmp : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ Ψ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ, (∀ a d b g, Ψ (pM a d b * g) = Ψ g) →
    ∀ T : GL (Ix n) O → GL (Ix n) (IsLocalRing.ResidueField O), (∀ κ, IsRed (O := O) w κ (T κ)) →
      avgK ϖ (fun κ => Ψ (T κ)) =
        sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) /
          sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) =>
            (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g))

def JpPos : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n r m : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β : Matrix (Fin n) (Fin n) k, β.rank = r →
    r ≤ m → ∃ x : ℝ, 0 < x ∧
      sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) = x

def JpCondition : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n r t : ℕ), r + t = n → 1 ≤ r →
    ∀ ψ₀ : AddChar (IsLocalRing.ResidueField O) ℂ, ψ₀ ≠ 1 →
    ∀ β : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), β.rank = r →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
      ∀ ℓ : IsLocalRing.ResidueField O → O, (∀ a, IsLocalRing.residue O (ℓ a) = a) →
      ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h →
      ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
        [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
        MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ z : ℂ,
        ∫ x, ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
          (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) ∂ν = c z

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KDKDelApply
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Kabs

theorem kD_kDel_apply {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]

end GlobalTheory.CompanionTheory.Kabs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic
section
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerLinear

theorem kerLin_of_kerBasic : KerBasic → KerLin := by
  intro hb X ι _ φ c hφ
  constructor
  · refine ⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩
    have key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))
      | cons a s ha ih =>
        have h1 : HasCompactSupport (fun y => φ a y * c a) :=
          (hφ a).2.mul_right
        have h2 := h1.add ih
        have h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) =
            (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i := by
          funext y
          simp [Finset.sum_cons]
        rw [h3]
        exact h2
    exact key Finset.univ
  · intro x y
    have hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite :=
      fun i => (hb X (φ i) (hφ i)).1 x y
    have hfin' : ∀ i ∈ (Finset.univ : Finset ι),
        (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite := fun i _ =>
      (hfin i).subset (Function.support_mul_subset_left _ _)
    unfold ker
    rw [finsum_sum_comm _ _ hfin']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mul]

end GlobalTheory.CompanionTheory.KerLinear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable
section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSubsetSumVanishesStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_subset_sum_vanishes : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | exact GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | (intros; apply GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex <;> assumption)
end

