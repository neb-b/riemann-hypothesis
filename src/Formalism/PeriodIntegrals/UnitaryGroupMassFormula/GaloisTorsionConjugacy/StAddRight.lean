module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def St (L L' : PeriodPair) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (t t' : ℂ) : Prop :=
  (t ∈ L.lattice ∧ t' ∈ L'.lattice) ∨
  (t ∉ L.lattice ∧ t' ∉ L'.lattice ∧ ∃ (hx : L.weierstrassP t ∈ M) (hy : L.derivWeierstrassP t ∈ M),
    L'.weierstrassP t' = ρ ⟨_, hx⟩ ∧ L'.derivWeierstrassP t' = ρ ⟨_, hy⟩)

section maps

variable {K K' : Type*} [Field K] [Field K']

theorem addX_map (φ : K →+* K') (x y x₂ y₂ : K) :
    φ (addX x y x₂ y₂) = addX (φ x) (φ y) (φ x₂) (φ y₂) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add (f := _), map_neg, map_ofNat]

theorem addY_map (φ : K →+* K') (x y x₂ y₂ : K) :
    φ (addY x y x₂ y₂) = addY (φ x) (φ y) (φ x₂) (φ y₂) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add (f := _), map_neg, map_ofNat]

theorem dblX_map (φ : K →+* K') (x y g : K) :
    φ (dblX x y g) = dblX (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add (f := _), map_neg, map_ofNat]

theorem dblY_map (φ : K →+* K') (x y g : K) :
    φ (dblY x y g) = dblY (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add (f := _), map_neg, map_ofNat]

end maps

theorem wp_add_mem (L : PeriodPair) (z : ℂ) {ω : ℂ} (h : ω ∈ L.lattice) :
    L.weierstrassP (z + ω) = L.weierstrassP z := PeriodPair.weierstrassP_add_coe L z ⟨ω, h⟩

theorem dwp_add_mem (L : PeriodPair) (z : ℂ) {ω : ℂ} (h : ω ∈ L.lattice) :
    L.derivWeierstrassP (z + ω) = L.derivWeierstrassP z := PeriodPair.derivWeierstrassP_add_coe L z ⟨ω, h⟩

theorem neg_pair (L : PeriodPair) {s r : ℂ} (h : s + r ∈ L.lattice) :
    L.weierstrassP r = L.weierstrassP s ∧ L.derivWeierstrassP r = -L.derivWeierstrassP s := by
  have hr : r = -s + (s + r) := by ring
  rw [hr, wp_add_mem L _ h, dwp_add_mem L _ h, PeriodPair.weierstrassP_neg,
    PeriodPair.derivWeierstrassP_neg]
  exact ⟨rfl, rfl⟩

theorem pInj (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    z - w ∈ L.lattice := by
  rcases (pInjective L z w hz hw).1 hx with h | h
  · exact h
  · have h1 := (neg_pair L h).2
    have h0 : L.derivWeierstrassP z = 0 := by linear_combination (hy + h1) / 2
    have h2 : 2 * z ∈ L.lattice := (pDerivZero L z hz).1 h0
    have e : z - w = 2 * z - (z + w) := by ring
    rw [e]
    exact L.lattice.sub_mem h2 h

theorem pNeg (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = -L.derivWeierstrassP w) :
    z + w ∈ L.lattice := by
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using L.lattice.neg_mem h)
  have h := pInj L hz hw' (by rw [PeriodPair.weierstrassP_neg, hx])
    (by rw [PeriodPair.derivWeierstrassP_neg, hy])
  simpa using h

section rel

variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem rho_inj {a b : M} (h : ρ a = ρ b) : a = b := ρ.toRingHom.injective h

theorem st_zero : St L L' M ρ 0 0 := Or.inl ⟨L.lattice.zero_mem, L'.lattice.zero_mem⟩

theorem st_mem_iff {t t' : ℂ} (h : St L L' M ρ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, _⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem st_add_right {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L'.lattice) :
    St L L' M ρ t (t' + ω) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨h1, L'.lattice.add_mem h2 hω⟩
  · refine Or.inr ⟨h1, fun hh => h2 (by simpa using L'.lattice.sub_mem hh hω), hx, hy, ?_, ?_⟩
    · rw [wp_add_mem L' t' hω, e1]
    · rw [dwp_add_mem L' t' hω, e2]

theorem st_add_left {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L.lattice) :
    St L L' M ρ (t + ω) t' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨L.lattice.add_mem h1 hω, h2⟩
  · have ex : L.weierstrassP (t + ω) = L.weierstrassP t := wp_add_mem L t hω
    have ey : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := dwp_add_mem L t hω
    have hx' : L.weierstrassP (t + ω) ∈ M := by rw [ex]; exact hx
    have hy' : L.derivWeierstrassP (t + ω) ∈ M := by rw [ey]; exact hy
    refine Or.inr ⟨fun hh => h1 (by simpa using L.lattice.sub_mem hh hω), h2, hx', hy', ?_, ?_⟩
    · rw [e1]
      congr 1
      exact Subtype.ext ex.symm
    · rw [e2]
      congr 1
      exact Subtype.ext ey.symm

theorem st_unique {t t₁ t₂ : ℂ} (h1 : St L L' M ρ t t₁) (h2 : St L L' M ρ t t₂) :
    t₁ - t₂ ∈ L'.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, _, _, _, _, _⟩
    · exact L'.lattice.sub_mem b1 b2
    · exact absurd a1 a2
  · rcases h2 with ⟨a2, _⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd a2 a1
    · exact pInj L' b1 b2 (by rw [e1, e2]) (by rw [f1, f2])

theorem st_inj {t u s : ℂ} (h1 : St L L' M ρ t s) (h2 : St L L' M ρ u s) :
    t - u ∈ L.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, _, _, _, _⟩
    · exact L.lattice.sub_mem a1 a2
    · exact absurd b1 b2
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd b2 b1
    · have gx := rho_inj (e1.symm.trans e2)
      have gy := rho_inj (f1.symm.trans f2)
      exact pInj L a1 a2 (congrArg Subtype.val gx) (congrArg Subtype.val gy)

theorem st_add (hA : AddLaw) (hD : DblLaw) (hg2 : L.g₂ ∈ M) (hg2' : L'.g₂ = ρ ⟨_, hg2⟩)
    {t t' u u' : ℂ} (ht : St L L' M ρ t t') (hu : St L L' M ρ u u') :
    St L L' M ρ (t + u) (t' + u') := by
  rcases ht with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · have := st_add_right (st_add_left hu a1) b1
    rwa [add_comm u t, add_comm u' t'] at this
  have ht : St L L' M ρ t t' := Or.inr ⟨a1, b1, hx1, hy1, e1, f1⟩
  rcases hu with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
  · exact st_add_right (st_add_left ht a2) b2
  have hu : St L L' M ρ u u' := Or.inr ⟨a2, b2, hx2, hy2, e2, f2⟩
  set X1 : M := ⟨_, hx1⟩
  set Y1 : M := ⟨_, hy1⟩
  set X2 : M := ⟨_, hx2⟩
  set Y2 : M := ⟨_, hy2⟩
  by_cases hs : t + u ∈ L.lattice
  · left
    refine ⟨hs, ?_⟩
    obtain ⟨p1, p2⟩ := neg_pair L hs
    have q1 : X2 = X1 := Subtype.ext p1
    have q2 : Y2 = -Y1 := Subtype.ext (by simp [Y1, Y2, p2])
    apply pNeg L' b1 b2
    · rw [e1, e2, q1]
    · rw [f1, f2, q2, map_neg, neg_neg]
  have hs' : t' + u' ∉ L'.lattice := by
    intro h
    obtain ⟨p1, p2⟩ := neg_pair L' h
    rw [e1, e2] at p1
    rw [f1, f2, ← map_neg] at p2
    have k1 := congrArg Subtype.val (rho_inj p1)
    have k2 := congrArg Subtype.val (rho_inj p2)
    have k : L.derivWeierstrassP u = -L.derivWeierstrassP t := k2
    exact hs (pNeg L a1 a2 k1.symm (by linear_combination k))
  right
  refine ⟨hs, hs', ?_⟩
  by_cases hd : t - u ∈ L.lattice
  ·
    have htu : St L L' M ρ t u' := by
      have := st_add_left hu hd
      rwa [show u + (t - u) = t by ring] at this
    have hd' : t' - u' ∈ L'.lattice := st_unique ht htu
    have h2 : 2 * t ∉ L.lattice := by
      intro h
      apply hs
      have := L.lattice.sub_mem h hd
      rwa [show 2 * t - (t - u) = t + u by ring] at this
    have h2' : 2 * t' ∉ L'.lattice := by
      intro h
      apply hs'
      have := L'.lattice.sub_mem h hd'
      rwa [show 2 * t' - (t' - u') = t' + u' by ring] at this
    have et : t + u = 2 * t + -(t - u) := by ring
    have et' : t' + u' = 2 * t' + -(t' - u') := by ring
    have n1 := L.lattice.neg_mem hd
    have n1' := L'.lattice.neg_mem hd'
    obtain ⟨d1, d2⟩ := hD L t a1 h2
    obtain ⟨d1', d2'⟩ := hD L' t' b1 h2'
    set G : M := ⟨_, hg2⟩
    have v1 : L.weierstrassP (t + u) = ((dblX X1 Y1 G : M) : ℂ) := by
      rw [et, wp_add_mem L _ n1, d1]
      exact (dblX_map (algebraMap M ℂ) X1 Y1 G).symm
    have v2 : L.derivWeierstrassP (t + u) = ((dblY X1 Y1 G : M) : ℂ) := by
      rw [et, dwp_add_mem L _ n1, d2]
      exact (dblY_map (algebraMap M ℂ) X1 Y1 G).symm
    refine ⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩
    · rw [et', wp_add_mem L' _ n1', d1', e1, f1, hg2']
      have : (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M)
          = dblX X1 Y1 G := Subtype.ext v1
      rw [this]
      exact (dblX_map (ρ : M →+* ℂ) X1 Y1 G).symm
    · rw [et', dwp_add_mem L' _ n1', d2', e1, f1, hg2']
      have : (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M)
          = dblY X1 Y1 G := Subtype.ext v2
      rw [this]
      exact (dblY_map (ρ : M →+* ℂ) X1 Y1 G).symm
  ·
    have hd' : t' - u' ∉ L'.lattice := by
      intro h
      have hut : St L L' M ρ u t' := by
        have := st_add_right hu h
        rwa [show u' + (t' - u') = t' by ring] at this
      exact hd (st_inj ht hut)
    obtain ⟨d1, d2⟩ := hA L t u a1 a2 hd hs
    obtain ⟨d1', d2'⟩ := hA L' t' u' b1 b2 hd' hs'
    have v1 : L.weierstrassP (t + u) = ((addX X1 Y1 X2 Y2 : M) : ℂ) := by
      rw [d1]
      exact (addX_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm
    have v2 : L.derivWeierstrassP (t + u) = ((addY X1 Y1 X2 Y2 : M) : ℂ) := by
      rw [d2]
      exact (addY_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm
    refine ⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩
    · rw [d1', e1, f1, e2, f2]
      have : (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M)
          = addX X1 Y1 X2 Y2 := Subtype.ext v1
      rw [this]
      exact (addX_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm
    · rw [d2', e1, f1, e2, f2]
      have : (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M)
          = addY X1 Y1 X2 Y2 := Subtype.ext v2
      rw [this]
      exact (addY_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm

theorem st_nsmul (hA : AddLaw) (hD : DblLaw) (hg2 : L.g₂ ∈ M) (hg2' : L'.g₂ = ρ ⟨_, hg2⟩)
    {t t' : ℂ} (h : St L L' M ρ t t') (n : ℕ) :
    St L L' M ρ ((n : ℂ) * t) ((n : ℂ) * t') := by
  induction n with
  | zero => simpa using (st_zero : St L L' M ρ 0 0)
  | succ n ih =>
    have h2 := st_add hA hD hg2 hg2' ih h
    have e1 : ((n + 1 : ℕ) : ℂ) * t = (n : ℂ) * t + t := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℂ) * t' = (n : ℂ) * t' + t' := by push_cast; ring
    rw [e1, e2]
    exact h2

theorem st_exists (hO : POnto) (hg2 : L.g₂ ∈ M) (hg3 : L.g₃ ∈ M)
    (hg2' : L'.g₂ = ρ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ ⟨_, hg3⟩) (t : ℂ)
    (ht : t ∈ L.lattice ∨ (L.weierstrassP t ∈ M ∧ L.derivWeierstrassP t ∈ M)) :
    ∃ t', St L L' M ρ t t' := by
  by_cases h : t ∈ L.lattice
  · exact ⟨0, Or.inl ⟨h, L'.lattice.zero_mem⟩⟩
  obtain ⟨hx, hy⟩ := ht.resolve_left h
  set X : M := ⟨_, hx⟩
  set Y : M := ⟨_, hy⟩
  have curve : Y ^ 2 = 4 * X ^ 3 - ⟨_, hg2⟩ * X - ⟨_, hg3⟩ :=
    Subtype.ext (by
      have e := L.derivWeierstrassP_sq t h
      have h4 : ((4 : M) : ℂ) = 4 := map_ofNat (algebraMap M ℂ) 4
      push_cast [X, Y, h4]
      linear_combination e)
  have curve' : (ρ Y) ^ 2 = 4 * (ρ X) ^ 3 - L'.g₂ * ρ X - L'.g₃ := by
    rw [hg2', hg3']
    have := congrArg ρ curve
    simpa [map_sub, map_mul, map_pow, map_ofNat] using this
  obtain ⟨z, hz, e1, e2⟩ := hO L' (ρ X) (ρ Y) curve'
  exact ⟨z, Or.inr ⟨h, hz, hx, hy, e1, e2⟩⟩

end rel

end PI.GalTorsConj.W

end
