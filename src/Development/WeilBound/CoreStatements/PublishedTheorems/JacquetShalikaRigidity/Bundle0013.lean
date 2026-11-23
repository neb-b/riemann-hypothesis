module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UpperBlockProducts
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace UpperBlockProducts

theorem blk_corner {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {j : ℕ} {g : GL (Fin a) R}
    (hg : GlobalTheory j g) : GlobalTheory j (cornerGL a s g) := by
  intro i c hic
  change (1 : Matrix (Fin a) (Fin a) S) i c - s ((1 : Matrix (Fin a) (Fin a) R) i c) + s (g.val i c) = _
  rw [hg i c hic, sub_add_cancel]

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blk_fl (v : Pl E) {j : ℕ} {c : GL (Fin k) (v.adicCompletion E)} (hc : GlobalTheory j c) : GlobalTheory j (fl k v c) :=
  blk_corner (sFin E) (blk_corner (sLoc E v) hc)

theorem posM_blk_zero {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : (c : ℕ) ≤ i) :
    posM Subtype.val Y i c = 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  obtain ⟨t1, t2, t3⟩ := t.2
  rw [h1, h2] at *
  omega

theorem uu_blkU {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU Y : GA E k) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · change (1 + posM Subtype.val Y) i c = 0
    rw [Matrix.add_apply, posM_blk_zero Y i c (le_of_lt hci), Matrix.one_apply_ne hci.ne', add_zero]
  · change (1 + posM Subtype.val Y) i i = 1
    rw [Matrix.add_apply, posM_blk_zero Y i i le_rfl, Matrix.one_apply_eq, add_zero]

theorem uu_mul {u u' : GA E k} (hu : UU 0 u) (hu' : UU 0 u') : UU 0 (u * u') := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hu'.1 l c (lt_of_lt_of_le hci h), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hu.2.1, hu'.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hu.1 i l h, zero_mul]
      · rw [hu'.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end UpperBlockProducts

open UpperBlockProducts UnipotentCharacter in
theorem finite_place_of_jump_windows : jumpWindows.S2 → jumpWindows.S9 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → FinitePlaceStep := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m v hv hmv hm0 U hU x C hxY hsm hlev hB
  obtain ⟨-, -, i3, i4, i5, -, i7, i8, -, i10, -, -, -, i14, -⟩ := hG0 E k
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E k ψ hψ
  obtain ⟨-, b2, b3, b4, b5⟩ := hG5b E k S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (v.adicCompletion E) k (m v + 1)
  obtain ⟨p2law, p2norm, p2uu, p2whit, -, p2good, -⟩ := hP2 E k ψ hψ
  obtain ⟨s0, sadd, ssmul, -, sT, -⟩ := hS2 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly
  let U' : Set (GL (Fin k) (v.adicCompletion E)) := {u | repW k v u (J x) = J x} ∩ (fl k v) ⁻¹' U
  have hU' : U' ∈ 𝓝 (1 : GL (Fin k) (v.adicCompletion E)) :=
    Filter.inter_mem (hlev v hv) ((i14 v).continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU))
  have hne : ∃ y, chi ψ v y ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc v
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, hηr, ⟨Cl, hClc, hClU, hClB, hCl⟩, hmain⟩ :=
    hS9 (v.adicCompletion E) k (m v) hmv (chi ψ v) (chi_cont hψ v) hne (XB E k) (repW k v) U' hU'
  have hClU' : ∀ c ∈ Cl, fl k v c ∈ U := fun c hc => (hClU hc).2
  have inS : ∀ u, InS S (fl k v u : GA E k) := fun u w hw => i5 v w u (fun e => hw (e ▸ hv))
  have stab : ∀ u, ∀ z ∈ Y, repW k v u z ∈ Y := fun u z hz => hY.stable _ (inS u) z hz
  have hJx' : J (∑ t ∈ T, c t • ρ (fl k v t) x) = ∑ t ∈ T, c t • repW k v t (J x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hW.inter, repW_apply]
  have hJY : J (∑ t ∈ T, c t • ρ (fl k v t) x) ∈ Y := by
    rw [hJx']
    exact Y.sum_mem fun t _ => Y.smul_mem _ (stab t _ hxY)
  have hgood' : Good ψ (k - 1) (J (∑ t ∈ T, c t • ρ (fl k v t) x)) := hY.good _ hJY
  have key : ∀ g' : GA E k, cLoc v g' = 1 → ∀ h, GlobalTheory (m v + 1) h →
      Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (g' * fl k v h) = η h * Wh ψ (J x) (g' * fl k v (r h)) := by
    intro g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Y, ∀ y : UnipotentBlockColumnIndex k (m v + 1) (m v + 1) → v.adicCompletion E,
        (Λ : XB E k →ₗ[ℂ] ℂ) (repW k v (blkU y) z) = chi ψ v (lastE (m v + 1) y) * (Λ : XB E k →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hY.good _ (stab _ z hz)),
        hΛ _ (hY.good _ hz), repW_apply, g5r, i8 v g' hg', i10,
        (g5c z (hY.good _ hz)).2.2 (m v + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain (J x) (fun u hu => hu.1) Y stab hxY (Λ : XB E k →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    have hsum : ∑ t ∈ T, c t • repW k v t (J x) ∈ Y := by rw [← hJx']; exact hJY
    rw [hΛ _ (hY.good _ (stab _ _ hsum)), hΛ _ (hY.good _ (stab _ _ hxY)),
      repW_apply, repW_apply, g5r, g5r] at this
    rw [hJx']
    exact this
  have hpre : Pre ψ 0 (Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x))) :=
    p2whit (k - 1) (by omega) _ (p2good _ _ hgood')
  have hlawW : ∀ u, UU 0 u → ∀ z, Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (u * z) =
      psN ψ u * Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) z :=
    fun u hu z => p2law 0 _ hpre u (p2uu u hu) z
  have hpsN : ∀ u : GA E k, psN ψ u ≠ 0 := fun u e0 => by
    have h1 := p2norm u
    rw [e0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨∑ t ∈ T, c t • ρ (fl k v t) x, fl k v '' Cl, ?_, hJY, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact hClU' c₂ hc₂
  · refine sum_of _ s0 sadd ssmul T c _ fun t => sT (ρ (fl k v t)) (fun g z => ?_) x hsm
    simp only [MonoidHom.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, i7 _ (i3 v t) g, map_mul, ContinuousLinearMap.mul_apply]
  · rw [hJx']
    exact sum_of _ b5 b4 b3 T c _ fun t => by rw [repW_apply]; exact b2 _ _ hlev
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact blk_fl v (hClB c₂ hc₂)
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hCb⟩ := hB
  refine ⟨hCc.mul (hClc.image (i14 v)), ?_, ?_, ?_⟩
  · rintro _ ⟨c₁, hc₁, _, ⟨c₂, hc₂, rfl⟩, rfl⟩ w hw
    rw [map_mul, hCS c₁ hc₁ w hw, inS c₂ w hw, one_mul]
  · have h1 := key 1 (map_one _) 1 s10blk1
    rw [hr1] at h1
    simp only [map_one, mul_one] at h1
    obtain ⟨s₁, hs₁, hηs₁⟩ := hηr 1
    have hs₁' : 0 < s₁ := lt_of_le_of_ne hs₁ fun e0 => hη1 (by rw [hηs₁, ← e0, Complex.ofReal_zero])
    refine ⟨s₁ * t₀, mul_pos hs₁' ht₀, ?_⟩
    rw [h1, hηs₁, hW1]
    push_cast
    ring
  · intro g hg hg0
    obtain ⟨hgI, hgL⟩ := hg
    have hgv : Mir (m v + 1) (cLoc v g) := by simpa using hgL v
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgv
    set g' : GA E k := g * (fl k v (cLoc v g))⁻¹ with hg'def
    have hg' : cLoc v g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have e : g = blkU (fun t => sFin E (sLoc E v (y t))) * (g' * fl k v h) := by
      rw [← i10, ← mul_assoc, ← i8 v g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
    have hWg : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) g =
        ψ (lastE (m v + 1) fun t => sFin E (sLoc E v (y t))) * (η h * Wh ψ (J x) (g' * fl k v (r h))) := by
      rw [e, (g5c _ hgood').2.2 (m v + 1) (Nat.succ_pos _), key g' hg' h hh]
    have hηh : η h ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    have hW'' : Wh ψ (J x) (g' * fl k v (r h)) ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    obtain ⟨c₂, hc₂, hhc⟩ := hCl h hh hηh
    have hOm : Om n m (g' * fl k v (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
        exact hgI
      · rcases eq_or_ne w v with rfl | hwv
        · rw [map_mul, hg', i4, one_mul]
          exact hrMir h hh hηh
        · rw [map_mul, hg'def, map_mul, map_inv, i5 v w _ hwv, i5 v w _ hwv, inv_one, mul_one, mul_one]
          simpa [hwv] using hgL w
    obtain ⟨nn₀, c₁, hc₁, t₁, hnn₀, hnnS, hgeq₀, ht₁, hWv⟩ := hCb _ hOm hW''
    obtain ⟨sh, hsh, hηsh⟩ := hηr h
    have hYg : (blkU fun t => sFin E (sLoc E v (y t)) : GA E k) = fl k v (blkU y) := (i10 v _ y).symm
    have h2 : nn₀ * (c₁ * fl k v c₂) = g' * fl k v h := by
      rw [hhc, map_mul, ← mul_assoc g', hgeq₀, mul_assoc]
    have hcc : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (c₁ * fl k v c₂) = ((sh * t₁ : ℝ) : ℂ) := by
      have h1 := hlawW nn₀ hnn₀ (c₁ * fl k v c₂)
      rw [h2, key g' hg' h hh, hWv, hηsh] at h1
      apply mul_left_cancel₀ (hpsN nn₀)
      rw [← h1]
      push_cast
      ring
    have huu : UU 0 ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀ : GA E k) := uu_mul (uu_blkU _) hnn₀
    refine ⟨(blkU fun t => sFin E (sLoc E v (y t))) * nn₀, c₁ * fl k v c₂,
      Set.mem_image2_of_mem hc₁ ⟨c₂, hc₂, rfl⟩, sh * t₁, huu, ?_, ?_, mul_nonneg hsh ht₁, ?_⟩
    · intro w hw
      rw [map_mul, hYg, i5 v w _ (fun e0 => hw (e0 ▸ hv)), hnnS w hw, one_mul]
    · rw [mul_assoc, h2]
      exact e
    · have hg2 : g = ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀) * (c₁ * fl k v c₂) := by
        rw [mul_assoc, h2]
        exact e
      rw [hg2, hlawW _ huu, hcc]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VolumeShellOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ShellSummation

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsMulLeftInvariant] (β : GA E k → ℝ≥0∞) (z : GA E k) :
    Measure.map (fun g => z * g) (μ.withDensity β) = μ.withDensity (fun g => β (z⁻¹ * g)) := by
  ext s hs
  have key := lintegral_mul_left_eq_self (μ := μ) (s.indicator fun g => β (z⁻¹ * g)) z
  rw [Measure.map_apply (measurable_const_mul z) hs, withDensity_apply _ (measurable_const_mul z hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_const_mul z hs), ← lintegral_indicator hs, ← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : z * x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun g => z * g) ⁻¹' s from hx),
      inv_mul_cancel_left]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun g => z * g) ⁻¹' s from hx)]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem wt_shift {ν : Measure (GA E k)} (β : GA E k → ℝ≥0∞) (hβ : IsWt ν β) (z : GA E k)
    (hz : ∀ g, z * g = g * z) : IsWt ν (fun g => β (z⁻¹ * g)) := by
  refine ⟨hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
  have hc : ∀ h : GA E k, z⁻¹ * (h * g) = h * (z⁻¹ * g) := fun h => by
    have : z⁻¹ * h = h * z⁻¹ := ((Commute.inv_left (hz h))).eq
    rw [← mul_assoc, this, mul_assoc]
  simp only [hc]
  exact hβ.2 _


omit [_root_.NumberField.IsTotallyComplex E] [NumberField E] in
variable (E k) in
def shell (a : ℝ) (j : ℤ) : Set (GA E k) :=
  {g | Real.exp (a * j) ≤ Dt g ∧ Dt g < Real.exp (a * j) * Real.exp a}

theorem exists_shell (a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    ∃ j : ℤ, Real.exp (a * j) ≤ D ∧ D < Real.exp (a * j) * Real.exp a := by
  refine ⟨⌊Real.log D / a⌋, ?_, ?_⟩
  · have h := Int.floor_le (Real.log D / a)
    rw [le_div_iff₀ ha] at h
    calc Real.exp (a * ⌊Real.log D / a⌋) ≤ Real.exp (Real.log D) :=
          Real.exp_le_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])
      _ = D := Real.exp_log hD
  · have h := Int.lt_floor_add_one (Real.log D / a)
    rw [div_lt_iff₀ ha] at h
    rw [← Real.exp_add]
    calc D = Real.exp (Real.log D) := (Real.exp_log hD).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])

theorem min_le_bnd (a ε D : ℝ) (ha : 0 < a) (hε : 0 < ε) (hD : 0 < D) (j : ℤ)
    (h1 : Real.exp (a * j) ≤ D) (h2 : D < Real.exp (a * j) * Real.exp a) :
    min D D⁻¹ ^ ε ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := by
  have key : min D D⁻¹ ≤ Real.exp (a - a * |(j : ℝ)|) := by
    rcases le_or_gt 0 (j : ℝ) with hj | hj
    · rw [abs_of_nonneg hj]
      calc min D D⁻¹ ≤ D⁻¹ := min_le_right _ _
        _ ≤ (Real.exp (a * j))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
        _ = Real.exp (-(a * j)) := (Real.exp_neg _).symm
        _ ≤ Real.exp (a - a * j) := Real.exp_le_exp.mpr (by linarith)
    · rw [abs_of_neg hj]
      calc min D D⁻¹ ≤ D := min_le_left _ _
        _ ≤ Real.exp (a * j) * Real.exp a := h2.le
        _ = Real.exp (a - a * -(j : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  calc min D D⁻¹ ^ ε ≤ Real.exp (a - a * |(j : ℝ)|) ^ ε :=
        Real.rpow_le_rpow (le_min hD.le (inv_nonneg.mpr hD.le)) key hε.le
    _ = Real.exp ((a - a * |(j : ℝ)|) * ε) := (Real.exp_mul _ _).symm
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem summ (c : ℝ) (hc : 0 < c) : Summable fun j : ℤ => Real.exp (-c * |(j : ℝ)|) := by
  have hr : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable fun n : ℕ => Real.exp (-c * n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).congr fun n => by
      rw [← Real.exp_nat_mul, mul_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hg
  · simpa using hg

end ShellSummation

open ShellSummation in
set_option synthInstance.maxHeartbeats 400000 in
theorem volume_shell_of : Q1 → Q2 → D0 → N3 → W0 → V1 := by
  intro hQ1 hQ2 hD0 hN3 hW0 E _ _ _ k μ _ hk β hβ
  obtain ⟨hpos, hmul, hcont, hrat, -, -, hcen, hcomm, -⟩ := hD0 E k
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).2.1 k le_rfl
  have hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | ∃ γ, ratGL E k γ = x} := by
    filter_upwards [hae] with h hh'
    obtain ⟨γ, u, -, hu, hh⟩ := hh'
    rw [hh, uu_eq_one le_rfl hu, mul_one]
    exact ⟨γ, rfl⟩
  have T1 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℝ≥0∞, Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi
    have := hQ1 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g)
    rw [this]
    simp only [lintegral_dirac, one_mul]
  have T2 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℂ, Measurable Φ → RatInv Φ →
      Integrable Φ (μ.withDensity β) → ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi hint
    have := (hQ2 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g) hint).2
    rw [this]
    simp only [integral_dirac, one_mul]
  have hshift : ∀ t, IsWt (nuB E k k) (fun g => β ((splitCentre E k t)⁻¹ * g)) := fun t =>
    wt_shift β hβ _ (hcomm t)
  have P1 : ∀ (t : ℝ) (Φ : GA E k → ℝ≥0∞), Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi
    rw [T1 _ (hshift t) Φ hΦ hΦi, ← map_wd μ β (splitCentre E k t),
      lintegral_map hΦ (measurable_const_mul _)]
  have P2 : ∀ (t : ℝ) (Φ : GA E k → ℂ), Measurable Φ → RatInv Φ → Integrable Φ (μ.withDensity β) →
      ∫ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi hint
    rw [T2 _ (hshift t) Φ hΦ hΦi hint, ← map_wd μ β (splitCentre E k t),
      integral_map (measurable_const_mul _).aemeasurable hΦ.aestronglyMeasurable]
  refine ⟨P1, P2, fun ε hε => ?_⟩
  obtain ⟨a, ha, hcen'⟩ : ∃ a : ℝ, 0 < a ∧ ∀ t, Dt (splitCentre E k t) = Real.exp (a * t) :=
    ⟨_, mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr Module.finrank_pos), hcen⟩
  have hD : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hz : ∀ t g, Dt (splitCentre E k t * g) = Real.exp (a * t) * Dt g := fun t g => by
    rw [hmul, hcen']
  have hband : MeasurableSet (band E k) := by
    rw [show band E k = {g | 1 ≤ Dt g} ∩ {g | Dt g < Dt (splitCentre E k 1)} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hS : ∀ j, MeasurableSet (shell E k a j) := fun j => by
    rw [show shell E k a j = {g | Real.exp (a * j) ≤ Dt g} ∩ {g | Dt g < Real.exp (a * j) * Real.exp a} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hBfin : μ.withDensity β (band E k) < ∞ := (hW0 E k μ hk).2 β hβ
  have hSμ : ∀ j, μ.withDensity β (shell E k a j) ≤ μ.withDensity β (band E k) := by
    intro j
    have hP := P1 (-(j : ℝ)) ((band E k).indicator 1) (measurable_one.indicator hband) (by
      intro γ g
      have hmem : ratGL E k γ * g ∈ band E k ↔ g ∈ band E k := by
        simp only [band, Set.mem_ofPred_eq, hmul, hrat, one_mul]
      by_cases hg : g ∈ band E k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]; rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.1 h))])
    rw [lintegral_indicator_one hband] at hP
    rw [← hP, ← lintegral_indicator_one (hS j)]
    refine lintegral_mono fun g => ?_
    refine Set.indicator_le (g := fun g => (band E k).indicator 1 (splitCentre E k (-(j : ℝ)) * g))
      (fun g hg => ?_) g
    simp only [shell, Set.mem_ofPred_eq] at hg
    obtain ⟨h1, h2⟩ := hg
    have e1 : Real.exp (a * -(j : ℝ)) * Real.exp (a * j) = 1 := by
      rw [← Real.exp_add, show a * -(j : ℝ) + a * j = 0 by ring, Real.exp_zero]
    have e0 : 0 < Real.exp (a * -(j : ℝ)) := Real.exp_pos _
    have hmem : splitCentre E k (-(j : ℝ)) * g ∈ band E k := by
      show 1 ≤ Dt _ ∧ Dt _ < Dt (splitCentre E k 1)
      rw [hz, hcen', mul_one]
      constructor
      · have := mul_le_mul_of_nonneg_left h1 e0.le
        linarith
      · have := mul_lt_mul_of_pos_left h2 e0
        rw [← mul_assoc, e1, one_mul] at this
        exact this
    rw [Set.indicator_of_mem hmem]
    exact le_rfl
  have hf : Measurable fun g : GA E k => min (Dt g) (Dt g)⁻¹ ^ ε := (hD.min hD.inv).pow_const ε
  have hsum := (summ (a * ε) (mul_pos ha hε)).mul_left (Real.exp (a * ε))
  have hnn : ∀ j : ℤ, 0 ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := fun j => by positivity
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ g, ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ ∂μ.withDensity β
      ≤ ∫⁻ g, ∑' j : ℤ, (shell E k a j).indicator
          (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g ∂μ.withDensity β := by
        refine lintegral_mono fun g => ?_
        obtain ⟨j, h1, h2⟩ := exists_shell a (Dt g) ha (hpos g)
        have hmem : g ∈ shell E k a j := by simp only [shell, Set.mem_ofPred_eq]; exact ⟨h1, h2⟩
        calc ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ = ENNReal.ofReal (min (Dt g) (Dt g)⁻¹ ^ ε) :=
              Real.enorm_eq_ofReal (Real.rpow_nonneg (le_min (hpos g).le (inv_nonneg.mpr (hpos g).le)) ε)
          _ ≤ ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) :=
              ENNReal.ofReal_le_ofReal (min_le_bnd a ε (Dt g) ha hε (hpos g) j h1 h2)
          _ = (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g :=
              by rw [Set.indicator_of_mem hmem]
          _ ≤ _ := ENNReal.le_tsum (f := fun j : ℤ => (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g) j
    _ = ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (shell E k a j) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable]
        exact tsum_congr fun j => lintegral_indicator_const (hS j) _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (band E k) := ENNReal.tsum_le_tsum fun j => by exact mul_le_mul_of_nonneg_left (hSμ j) (zero_le)
    _ = (∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) *
          μ.withDensity β (band E k) := ENNReal.tsum_mul_right
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ hBfin
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        exact ENNReal.ofReal_lt_top

end PositivityTheory.AdelicQuotientData

end
end

