module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotent
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.Dilation

variable {k r : ℕ}

def dd (k r : ℕ) (τ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then ((r - i.val : ℕ) : ℤ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℤ)

theorem dil_eq (τ : ℝ) : dil k r τ = Matrix.diagonal (dd k r τ) := rfl

theorem dd_eq_zpow {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i = (τ : ℂ) ^ wt k r i := by
  unfold dd wt
  split_ifs
  · rw [_root_.zpow_natCast]
  · rw [_root_.zpow_zero]
  · rw [_root_.zpow_neg, _root_.zpow_natCast]

theorem dd_inv_mul {τ : ℝ} (hτ : τ ≠ 0) (i j : Fin (2 * r + k + 1)) :
    dd k r τ⁻¹ i * dd k r τ j = (τ : ℂ) ^ (wt k r j - wt k r i) := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow (inv_ne_zero hτ), dd_eq_zpow hτ, Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    neg_add_eq_sub]

theorem dd_mul_inv {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i * dd k r τ⁻¹ i = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow hτ, dd_eq_zpow (inv_ne_zero hτ), Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    add_neg_cancel, _root_.zpow_zero]

theorem star_dd (τ : ℝ) (i : Fin (2 * r + k + 1)) : star (dd k r τ i) = dd k r τ i := by
  unfold dd
  split_ifs <;> simp

theorem dd_pair {τ : ℝ} (hτ : τ ≠ 0) {i j : Fin (2 * r + k + 1)} (h : i.val < r ∨ j.val < r)
    (hs : i.val + j.val = 2 * r + k) : dd k r τ i * dd k r τ j = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have hw : wt k r i + wt k r j = 0 := by
    have := i.isLt
    have := j.isLt
    unfold wt
    split_ifs <;> omega
  rw [dd_eq_zpow hτ, dd_eq_zpow hτ, ← _root_.zpow_add₀ h0, hw, _root_.zpow_zero]

theorem dd_middle (τ : ℝ) {i : Fin (2 * r + k + 1)} (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    dd k r τ i = 1 := by
  unfold dd
  rw [if_neg (by omega), if_pos h2]

theorem dil_entry (a b : ℝ) (m : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (dil k r a * m * dil k r b) i j = dd k r a i * m i j * dd k r b j := by
  rw [dil_eq, dil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dil_mul_inv {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ * dil k r τ⁻¹ = 1 := by
  rw [dil_eq, dil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dd_mul_inv hτ i

theorem dil_inv {τ : ℝ} (hτ : τ ≠ 0) : (dil k r τ)⁻¹ = dil k r τ⁻¹ := by
  exact Matrix.inv_eq_right_inv (dil_mul_inv hτ)

theorem uh_mul {g h : Mat k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem dil_mem {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ ∈ UH (Hpk k r) := by
  show (dil k r τ)ᴴ * Hpk k r * dil k r τ = Hpk k r
  ext i j
  rw [dil_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, star_dd]
  by_cases h1 : (i.val < r ∨ j.val < r) ∧ i.val + j.val = 2 * r + k
  · rw [mul_right_comm, dd_pair hτ h1.1 h1.2, one_mul]
  · by_cases h2 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
    · obtain ⟨hr, hk, rfl⟩ := h2
      rw [dd_middle τ hr hk, one_mul, mul_one]
    · have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (fun hc => h1 ⟨Or.inl hc.1, hc.2⟩), if_neg (fun hc => h1 ⟨Or.inr hc.1, hc.2⟩),
          if_neg h2]
      rw [h0, mul_zero, zero_mul]

theorem Hpk_row {i p t : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val)
    (hs : i.val + p.val = 2 * r + k) : Hpk k r p t = if t = i then 1 else 0 := by
  have hpo : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
  simp only [Hpk]
  rcases eq_or_ne t i with rfl | hti
  · rw [if_pos rfl]
    rcases h with h | h
    · rw [if_neg (by omega), if_pos ⟨h, by omega⟩]
    · rw [if_pos ⟨by omega, by omega⟩]
  · have hv : t.val ≠ i.val := fun e => hti (Fin.ext e)
    rw [if_neg hti, if_neg (by omega), if_neg (by omega), if_neg (fun hc => hpo ⟨hc.1, hc.2.1⟩)]

theorem uw_col {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1)} (hp : p.val < r ∨ r + k < p.val) (s : Fin (2 * r + k + 1)) :
    h s p = if s = p then 1 else 0 := by
  have hcol : ∀ q : Fin (2 * r + k + 1), h *ᵥ bvec q = bvec q → h s q = if s = q then 1 else 0 := by
    intro q hq
    have e := congrFun hq s
    simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using e
  have hpl := p.isLt
  rcases hp with hp | hp
  · have hq : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have := (hh.2.1 ⟨p.val, hp⟩).1
    rw [hq] at this
    exact hcol p this
  · have hq : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have := (hh.2.1 ⟨2 * r + k - p.val, by omega⟩).2
    rw [hq] at this
    exact hcol p this

theorem uw_zero {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    h i j = 0 := by
  have hil := i.isLt
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  let p : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hpv : p.val = 2 * r + k - i.val := rfl
  have hpo : p.val < r ∨ r + k < p.val := by omega
  have hip : i.val + p.val = 2 * r + k := by omega
  have hcol := uw_col hh hpo
  have hrow : ∀ t, Hpk k r p t = if t = i then 1 else 0 := fun t => Hpk_row hi hip
  have hleft : ∀ t, (hᴴ * Hpk k r) p t = Hpk k r p t := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [Matrix.conjTranspose_apply, hcol]
    · intro s _ hs
      simp [Matrix.conjTranspose_apply, hcol, hs]
    · simp
  have e := congrFun (congrFun hU p) j
  rw [Matrix.mul_apply] at e
  simp only [hleft, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  have hji : j ≠ i := fun hc => by subst hc; omega
  rw [if_neg hji] at e
  exact e

theorem dil_comm {z : Fin (2 * r + k + 1) → ℂ} (τ : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    dil k r τ * h = h * dil k r τ := by
  ext i j
  rw [dil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [uw_col hh hj i]
    split_ifs with e
    · subst e
      rw [one_mul, mul_one]
    · rw [mul_zero, zero_mul]
  · have hj' : r ≤ j.val ∧ j.val ≤ r + k := by omega
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_zero hh hi hj'.1 hj'.2, mul_zero, zero_mul]
    · rw [dd_middle τ (by omega) (by omega), dd_middle τ hj'.1 hj'.2, one_mul, mul_one]

private theorem conj_mem_lemma {τ : ℝ} (hτ : τ ≠ 0) (m : Mat k r) (i j : Fin (2 * r + k + 1))
    (h : m i j = if i = j then 1 else 0) :
    (dil k r τ * m * dil k r τ⁻¹) i j = if i = j then 1 else 0 := by
  rw [dil_entry, h]
  split_ifs with e
  · subst e
    rw [mul_one, dd_mul_inv hτ]
  · rw [mul_zero, zero_mul]

theorem conj_mem {τ : ℝ} (hτ : τ ≠ 0) {m : Mat k r} (hm : m ∈ Nset k r) :
    dil k r τ * m * dil k r τ⁻¹ ∈ Nset k r := by
  have hU : m ∈ UH (Hpk k r) := hm.1
  have hc : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      m i (eI k r a) = if i = eI k r a then 1 else 0 := hm.2.1
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  refine ⟨uh_mul (uh_mul (dil_mem hτ) hU) (dil_mem (inv_ne_zero hτ)), ?_, ?_⟩
  · intro a i hai
    exact conj_mem_lemma hτ m i _ (hc a i hai)
  · intro i j h1 h2 h3
    exact conj_mem_lemma hτ m i j (hb i j h1 h2 h3)

theorem wt_lt {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hn : ¬ (r ≤ i.val ∧ j.val ≤ r + k)) :
    wt k r j + 1 ≤ wt k r i := by
  unfold wt
  split_ifs <;> omega

private theorem apply_self_eq_one_of_mem_Nset {m : Mat k r} (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1)) :
    m i i = if i = i then 1 else 0 :=
  Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i i le_rfl

theorem contract {τ : ℝ} (hτ : 1 ≤ τ) {m : Mat k r} (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) :
    ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖ := by
  have hpos : 0 < τ := by linarith
  have hτ0 : τ ≠ 0 := hpos.ne'
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  rw [dil_inv hτ0, Matrix.sub_apply, Matrix.sub_apply, dil_entry, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hij' : i.val < j.val := hij
    rw [if_neg hij.ne, sub_zero, sub_zero]
    by_cases hmid : r ≤ i.val ∧ j.val ≤ r + k
    · have h0 : m i j = 0 := by
        have e := hb i j (by omega) hmid.2 hmid.1
        rwa [if_neg hij.ne] at e
      rw [h0]
      simp
    · have hw := wt_lt (k := k) (r := r) hij' hmid
      rw [mul_right_comm, dd_inv_mul hτ0, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← _root_.zpow_neg_one]
      exact _root_.zpow_le_zpow_right₀ hτ (by omega)
  · have h1 : m i i = 1 := by simpa using apply_self_eq_one_of_mem_Nset hm i
    rw [h1, if_pos rfl, mul_one, dd_inv_mul hτ0, sub_self, _root_.zpow_zero]
    simp
  · have h0 : m i j = 0 := by
      have e := Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i j hij.le
      rwa [if_neg hij.ne'] at e
    rw [if_neg hij.ne', h0]
    simp

theorem main : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  intro k r z _
  refine ⟨fun τ hτ => ⟨dil_mem hτ.ne', fun h hh => dil_comm τ hh, fun m hm => ⟨?_, ?_⟩⟩,
    fun τ hτ m hm i j => contract hτ hm i j⟩
  · rw [dil_inv hτ.ne']
    exact conj_mem hτ.ne' hm
  · have e := conj_mem (inv_ne_zero hτ.ne') hm
    rwa [inv_inv, ← dil_inv hτ.ne'] at e

end GlobalTheory.SgInf.Dilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.CountSteps

section Abstract

variable {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ρ : V →+ E} {L : Submodule R V}

theorem strict_eq (hL : IsLat ρ L) (θ : ℝ) :
    ∃ θ₀, θ < θ₀ ∧ ∀ θ', θ < θ' → θ' ≤ θ₀ →
      sSup {N : Submodule R V | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} = hnStep ρ L θ' := by

  obtain ⟨t, ht, hsup⟩ :=
    finSup R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} hL (fun N hN => hN.1)
  obtain ⟨θ₀, hθ₀, hle⟩ : ∃ θ₀, θ < θ₀ ∧ ∀ N ∈ t, θ₀ ≤ muMin ρ N := by
    rcases t.eq_empty_or_nonempty with h | h
    · exact ⟨θ + 1, by linarith, by simp [h]⟩
    · obtain ⟨N₀, hN₀, hmin⟩ := t.exists_min_image (fun N => muMin ρ N) h
      exact ⟨muMin ρ N₀, (ht hN₀).2.2, hmin⟩
  refine ⟨θ₀, hθ₀, fun θ' h1 h2 => le_antisymm ?_ ?_⟩
  · rw [hsup]
    unfold hnStep
    refine Finset.sup_le fun N hN => ?_
    exact le_sSup ⟨(ht hN).1, (ht hN).2.1, h2.trans (hle N hN)⟩
  · unfold hnStep
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, lt_of_lt_of_le h1 hN.2.2⟩

private lemma zl_mono' {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨a, h ha, rfl⟩

theorem isSat_of_le {S N : Submodule R V} (hS : IsSat ρ L S) (h1 : S ≤ N) (h2 : N ≤ L) :
    IsSat ρ N S := by
  unfold IsSat Formalism.F.IsSaturated at *
  exact ⟨h1, zl_mono' h1, fun y hy hspan => hS.2.2 y (zl_mono' h2 hy) hspan⟩

theorem quot_slope_lt (hL : IsLat ρ L) (θ : ℝ) {N : Submodule R V} (h1 : hnStep ρ L θ < N) (h2 : N ≤ L) :
    Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ))) < θ := by
  obtain ⟨hsat, -, -, hmax⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, hsatEq, -, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨-, -, -, -, -, -, -, hq⟩ := satBasic R V E ρ N (hsub N h2)
  obtain ⟨hrk, hrkle, hdeg⟩ := hq _ (isSat_of_le hsat h1.le h2)

  have hne : rk ρ (hnStep ρ L θ) ≠ rk ρ N := fun h => h1.ne (hsatEq _ _ hsat h1.le h2 h.symm).symm
  have hlt : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ N := by exact_mod_cast lt_of_le_of_ne hrkle hne
  have key := hmax N h1 h2
  unfold Formalism.F.slope
  rw [hrk, hdeg, Nat.cast_sub hrkle, div_lt_iff₀ (by linarith)]
  exact key

theorem step_eq_bot (hL : IsLat ρ L) (h0 : L ≠ ⊥) (θ : ℝ) : hnStep ρ L θ = ⊥ ↔ muMax ρ L < θ := by
  obtain ⟨hsat, hmin, hcont, -⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, -, hrk0, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨hmaxL, -, ⟨N, hNsat, hN0, hNslope⟩, -, -⟩ := muChar R V E ρ L hL h0
  have hdegL : ∀ S : Submodule R V, S ≤ L → deg ρ S ≤ muMax ρ L * rk ρ S := (hmaxL _).1 le_rfl
  constructor
  · intro hbot
    by_contra hcon
    push Not at hcon

    have hNL : N ≤ L := hNsat.1
    obtain ⟨-, hminN, -, -, -⟩ := muChar R V E ρ N (hsub N hNL) hN0
    have hrkpos : (0 : ℝ) < rk ρ N := by
      have : rk ρ N ≠ 0 := fun h => hN0 ((hrk0 N hNL).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
      have e : slope ρ N = deg ρ N / rk ρ N := rfl
      rw [e, div_eq_iff hrkpos.ne'] at hNslope
      exact hNslope
    have hmm : muMax ρ L ≤ muMin ρ N := (hminN _).2 fun S hS => by
      have := hdegL S (hS.trans hNL)
      rw [mul_sub, ← hdegN]
      linarith
    have hle := hcont N hNL hN0 (hcon.trans hmm)
    rw [hbot] at hle
    exact hN0 (le_bot_iff.mp hle)
  · intro hlt
    by_contra hne
    have hH := hmin hne
    have hHL : hnStep ρ L θ ≤ L := hsat.1
    obtain ⟨hmaxH, -, -, hm1, hm2⟩ := muChar R V E ρ _ (hsub _ hHL) hne
    have : muMax ρ (hnStep ρ L θ) ≤ muMax ρ L :=
      (hmaxH _).2 fun S hS => hdegL S (hS.trans hHL)
    linarith

end Abstract

theorem exp_le_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) ≤ t ↔ c - Real.log t ≤ m := by
  rw [← Real.le_log_iff_exp_le ht]
  constructor <;> intro h <;> linarith

theorem exp_lt_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) < t ↔ c - Real.log t < m := by
  rw [← Real.lt_log_iff_exp_lt ht]
  constructor <;> intro h <;> linarith

theorem steps : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  intro I x t ht
  obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  obtain ⟨hTC, -, -, -, hw⟩ := _root_.GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have := hTC
  have hdet : ∀ w, IsUnit (frm I x w).det := fun w => (hw w).1
  set ρ := Formalism.HermitianLatticesTheory.realize (bas I) (frm I x) with hρ
  set L := lamX I x with hLdef
  have hLlat : IsLat ρ L := (plLat _ _ _ (bas I) (frm I x) hdet L hfg).1
  have : IsNoetherian (𝓞 I.E) L := isNoetherian_of_fg_of_noetherian L hfg
  have hNfg : ∀ N, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le_of_isNoetherian hN
  set c : ℝ := Real.log 2 / 2 - logDisc I.E / (2 * (Module.finrank ℚ I.E : ℝ)) with hc

  have hlarge : ∀ N, N ≤ L → N ≠ ⊥ →
      largestSize (bas I) (frm I x) N = Real.exp (c - muMin ρ N) := fun N hN h0 =>
    (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.2.2.1
  have hsq : ∀ N S, N ≤ L → N ≠ ⊥ → IsSat ρ N S → S ≠ N →
      sizeQ (bas I) (frm I x) N S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ S))) :=
    fun N S hN h0 hS hne => (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.1 S hS hne
  set θ := c - Real.log t with hθ

  have hLe : stepLe I x t = hnStep ρ L θ := by
    unfold stepLe hnStep
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_le_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_le_iff ht).2 hs
  have hLt : stepLt I x t = sSup {N : Submodule (𝓞 I.E) (Fin I.n → I.E) |
      N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} := by
    unfold stepLt
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_lt_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_lt_iff ht).2 hs
  obtain ⟨θ₀, hθ₀, hstrict⟩ := strict_eq hLlat θ
  have hLt' : stepLt I x t = hnStep ρ L θ₀ := hLt.trans (hstrict θ₀ hθ₀ le_rfl)
  have hsame : ∀ θ', θ < θ' → θ' ≤ θ₀ → hnStep ρ L θ' = hnStep ρ L θ₀ := fun θ' h1 h2 =>
    (hstrict θ' h1 h2).symm.trans (hstrict θ₀ hθ₀ le_rfl)
  have hspec := hnStep_spec _ _ _ ρ L hLlat θ
  have hspec₀ := hnStep_spec _ _ _ ρ L hLlat θ₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLe]; exact hspec.1
  · rw [hLt']; exact hspec₀.1
  · unfold stepLt stepLe
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.le⟩
  · intro t' htt'
    unfold stepLe stepLt
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.trans_lt htt'⟩
  · intro h0
    rw [hLe] at h0 ⊢
    rw [hlarge _ hspec.1.1 h0]
    exact (exp_le_iff ht).2 (hspec.2.1 h0)
  · intro h0
    rw [hLt'] at h0 ⊢
    rw [hlarge _ hspec₀.1.1 h0]
    exact (exp_lt_iff ht).2 (lt_of_lt_of_le hθ₀ (hspec₀.2.1 h0))
  · intro N h1 h2
    rw [hLe] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec.1 h1.le h2) h1.ne]
    have hs := quot_slope_lt hLlat θ h1 h2
    exact (Real.log_lt_iff_lt_exp ht).1 (by linarith)
  · intro N h1 h2
    rw [hLt'] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec₀.1 h1.le h2) h1.ne]

    have key : ∀ θ', θ < θ' → θ' ≤ θ₀ →
        Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) < θ' := fun θ' h1' h2' => by
      have e := hsame θ' h1' h2'
      have := quot_slope_lt hLlat θ' (by rw [e]; exact h1) h2
      rwa [e] at this
    generalize Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) = s at key ⊢
    have hs : s ≤ θ := by
      by_contra hcon
      push Not at hcon
      have := key (min s θ₀) (lt_min hcon hθ₀) (min_le_right _ _)
      exact lt_irrefl _ (this.trans_le (min_le_left _ _))
    exact (Real.log_le_iff_le_exp ht).1 (by linarith)
  · intro hn
    have hL0 : L ≠ ⊥ := by
      intro h
      have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      have htop : (⊤ : Submodule I.E (Fin I.n → I.E)) = ⊥ := by
        rw [← hspan, h]
        simp
      exact top_ne_bot htop
    have hleast : least I x = Real.exp (c - muMax ρ L) := by
      unfold least
      exact (sizeMu _ _ _ (bas I) (frm I x) hdet L hfg hL0).2.2.2.1
    refine ⟨by rw [hleast]; exact Real.exp_pos _, ?_, ?_⟩
    · rw [hLe, step_eq_bot hLlat hL0, hleast, ← Real.log_lt_iff_lt_exp ht]
      constructor <;> intro h <;> linarith
    · rw [hLt', hleast, ← Real.log_le_iff_le_exp ht]
      constructor
      · intro hb
        by_contra hcon
        push Not at hcon
        have h1 : θ < muMax ρ L := by linarith
        have hm : muMax ρ L < θ₀ := (step_eq_bot hLlat hL0 θ₀).1 hb
        have := (step_eq_bot hLlat hL0 _).1 ((hsame _ h1 hm.le).trans hb)
        exact lt_irrefl _ this
      · intro h
        exact (step_eq_bot hLlat hL0 θ₀).2 (by linarith)

end GlobalTheory.CountSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_cutoff_fibre_integral_one_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  first | exact @GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | exact GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one | (intros; apply GlobalTheory.Dec.exists_measurable_cutoff_fibre_integral_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_frame_of_flag_alt : ∀ (n a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) → ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  first | exact @GlobalTheory.exists_orthonormal_frame_of_flag | exact GlobalTheory.exists_orthonormal_frame_of_flag | (intros; apply GlobalTheory.exists_orthonormal_frame_of_flag <;> assumption)
end

