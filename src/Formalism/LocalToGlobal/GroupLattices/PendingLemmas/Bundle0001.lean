module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ICIntCp

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
section
noncomputable section

namespace Formalism.L2.G.Pend

open MvPowerSeries Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem wToC_eq : (k0ToC p).comp (algebraMap (WW p) (K0 p)) = wToC p := RingHom.ext (witt_fraction_to_Cp_algebraMap p)

theorem coeff_one_l_ne (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) : PowerSeries.coeff 1 g.l ≠ 0 := by
  intro h
  have hE : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hd : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ g.l := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_l g
    · exact h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨e', he'⟩ := PowerSeries.X_dvd_iff.2 hex
  have h1 : PowerSeries.subst g.ex g.l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * (e' ^ 2 * PowerSeries.subst g.ex m) := by
    rw [hm, PowerSeries.subst_mul hE, PowerSeries.subst_pow hE, PowerSeries.subst_X hE]
    nth_rewrite 1 [he']
    ring
  rw [hinv] at h1
  have h2 := congrArg (PowerSeries.coeff 1) h1
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_X_pow_mul'] at h2
  simp at h2

theorem ex_l (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) :
    PowerSeries.subst g.l g.ex = PowerSeries.X := by
  have hE : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hL : PowerSeries.HasSubst g.l := PowerSeries.HasSubst.of_constantCoeff_zero' (cc_l g)
  have hu : IsUnit (PowerSeries.coeff 1 g.l) := (coeff_one_l_ne g hex hinv).isUnit
  have hQ : PowerSeries.subst g.l (g.l.substInvOfIsUnit hu) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left g.l (cc_l g) hu
  have h1 : g.ex = g.l.substInvOfIsUnit hu := by
    calc g.ex = PowerSeries.subst g.ex (PowerSeries.X : PowerSeries ℂ_[p]) := (PowerSeries.subst_X hE).symm
      _ = PowerSeries.subst g.ex (PowerSeries.subst g.l (g.l.substInvOfIsUnit hu)) := by rw [hQ]
      _ = PowerSeries.subst (PowerSeries.subst g.ex g.l) (g.l.substInvOfIsUnit hu) :=
          PowerSeries.subst_comp_subst_apply hL hE _
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) (g.l.substInvOfIsUnit hu) := by rw [hinv]
      _ = g.l.substInvOfIsUnit hu := PowerSeries.X_subst _
  rw [h1]
  exact hQ

theorem pt_lg (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : g.pt (g.lg a) = a := by
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (cc_l g))
    (PowerSeries.HasSubst.of_constantCoeff_zero ha), ex_l g hex hinv,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)]

def LTIso : Prop :=
  ∃ (ep : (WW p)ˣ) (th : PowerSeries (WW p)), PowerSeries.constantCoeff th = 0 ∧ IsUnit (PowerSeries.coeff 1 th) ∧
    PowerSeries.subst (PowerSeries.map (wToC p) th) (PowerSeries.map (k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p)) =
      PowerSeries.C (wToC p (ep : WW p)) * g.l

variable {g}

def epOf (h : LTIso g) : (WW p)ˣ := h.choose

def thOf (h : LTIso g) : PowerSeries (WW p) := h.choose_spec.choose

theorem thOf_zero (h : LTIso g) : PowerSeries.constantCoeff (thOf h) = 0 := h.choose_spec.choose_spec.1

theorem thOf_unit (h : LTIso g) : IsUnit (PowerSeries.coeff 1 (thOf h)) := h.choose_spec.choose_spec.2.1

theorem thOf_log (h : LTIso g) :
    PowerSeries.subst (PowerSeries.map (wToC p) (thOf h)) (PowerSeries.map (k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p)) =
      PowerSeries.C (wToC p (epOf h : WW p)) * g.l := h.choose_spec.choose_spec.2.2

theorem wToC_unit_ne (u : (WW p)ˣ) : wToC p (u : WW p) ≠ 0 := (u.isUnit.map (wToC p)).ne_zero

variable (g)

def beC (ep : ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  g.be (g.pt (C ep⁻¹ * X (0 : Fin 2))) (g.pt (C ep⁻¹ * X (1 : Fin 2)))

theorem beC_tie (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {ep : ℂ_[p]} (hep : ep ≠ 0) :
    subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (beC g ep) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)) := by
  have hT : HasSubst (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] :
      Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    hs2 (by rw [map_mul, cc_lg g (by simp), mul_zero]) (by rw [map_mul, cc_lg g (by simp), mul_zero])
  have h0 : ∀ i : Fin 2, constantCoeff (C ep⁻¹ * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    intro i
    rw [map_mul, constantCoeff_X, mul_zero]
  have hc : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], C ep⁻¹ * (C ep * a) = a := by
    intro a
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hep, map_one, one_mul]
  unfold beC
  rw [be_subst g hex hT (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1)), pt_subst g hT (h0 0), pt_subst g hT (h0 1),
    subst_mul hT, subst_mul hT, subst_C, subst_X hT, subst_X hT]
  show g.be (g.pt (C ep⁻¹ * (C ep * g.lg (X (0 : Fin 2))))) (g.pt (C ep⁻¹ * (C ep * g.lg (X (1 : Fin 2))))) = _
  rw [hc, hc, pt_lg g hex hinv (by simp), pt_lg g hex hinv (by simp)]

def BeRat (ep : ℂ_[p]) : Prop := ∃ b : MvPowerSeries (Fin 2) (K0 p), map (k0ToC p) b = beC g ep

def beOf (ep : ℂ_[p]) : MvPowerSeries (Fin 2) (K0 p) :=
  open Classical in if h : BeRat g ep then h.choose else 0

variable {g}

theorem map_beOf {ep : ℂ_[p]} (h : BeRat g ep) : map (k0ToC p) (beOf g ep) = beC g ep := by
  unfold beOf
  rw [dite_eq_left h]
  exact h.choose_spec

theorem be_tie (hOk : g.Ok) {ep : ℂ_[p]} (hep : ep ≠ 0) (h : BeRat g ep) :
    subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map (k0ToC p) (beOf g ep)) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)) := by
  rw [map_beOf h]
  exact beC_tie g hOk.2.2.1 hOk.2.2.2 hep

def beLT (h : LTIso g) : MvPowerSeries (Fin 2) (K0 p) := beOf g (wToC p (epOf h : WW p))

end Formalism.L2.G.Pend
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable (p : ℕ) [hp : Fact p.Prime]

def OcC : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by
    show ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := fun {a b} ha hb => by
    show ‖a + b‖ ≤ 1
    exact le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)
  zero_mem' := by
    show ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rw [norm_neg]
    exact ha

variable {p}

theorem mem_OcC (x : ℂ_[p]) : x ∈ OcC p ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem OcC_val (x : ℂ_[p]) : x ∈ OcC p ∨ x⁻¹ ∈ OcC p := by
  rcases le_total ‖x‖ 1 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem OcC_rank1 (x : ℂ_[p]) (hx : x ≠ 0) :
    (∃ n : ℕ, (p : ℂ_[p]) ^ n / x ∈ OcC p) ∧ (x⁻¹ ∉ OcC p → ∃ n : ℕ, x ^ n / (p : ℂ_[p]) ∈ OcC p) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  constructor
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (norm_p_lt_one (p := p))
    refine ⟨n, ?_⟩
    show ‖(p : ℂ_[p]) ^ n / x‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one hx0]
    exact hn.le
  · intro h
    have h1 : ‖x‖ < 1 := by
      by_contra hc
      refine h ?_
      show ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hc)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_p_pos (p := p)) h1
    refine ⟨n, ?_⟩
    show ‖x ^ n / (p : ℂ_[p])‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one norm_p_pos]
    exact hn.le

section Emb

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (i : Kf →+* ℂ_[p]) (hi : ∀ x : O, ‖i (algebraMap O Kf x)‖ ≤ 1)

include hi

theorem norm_unit (u : Oˣ) : ‖i (algebraMap O Kf (u : O))‖ = 1 := by
  refine le_antisymm (hi _) ?_
  have h1 : i (algebraMap O Kf (u : O)) * i (algebraMap O Kf ((u⁻¹ : Oˣ) : O)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  calc (1 : ℝ) = ‖i (algebraMap O Kf (u : O))‖ * ‖i (algebraMap O Kf ((u⁻¹ : Oˣ) : O))‖ := h2.symm
    _ ≤ ‖i (algebraMap O Kf (u : O))‖ * 1 := mul_le_mul_of_nonneg_left (hi _) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_nonunit {y : O} (hy : ¬ IsUnit y) : ‖i (algebraMap O Kf y)‖ < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : (p : O) ≠ 0 := by
    intro h0
    have := congrArg (fun z => i (algebraMap O Kf z)) h0
    simp only [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℂ_[p]) ≠ 0) this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  obtain ⟨u, hu⟩ := he.symm
  have hϖ1 : ‖i (algebraMap O Kf ϖ)‖ < 1 := by
    by_contra hc
    have h1 : ‖i (algebraMap O Kf ϖ)‖ = 1 := le_antisymm (hi _) (not_lt.1 hc)
    have h2 := congrArg (fun t => ‖i (algebraMap O Kf t)‖) hu
    simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    rw [h1, norm_unit i hi u, one_pow, one_mul] at h2
    exact absurd h2.symm (ne_of_lt (norm_p_lt_one (p := p)))
  have hy1 : ϖ ∣ y := by
    have : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).2 hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨z, rfl⟩ := hy1
  rw [map_mul, map_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hi z)) hϖ1

theorem norm_le_one_iff [IsFractionRing O Kf] (x : Kf) : ‖i x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap O Kf) := by
  constructor
  · intro hx
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨y, hy⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hu : IsUnit y
      · obtain ⟨u, rfl⟩ := hu
        refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
        have h1 : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (eq_of_mul_inv_eq_one h1)
      · exfalso
        have h1 := norm_nonunit i hi hu
        rw [hy, map_inv₀, norm_inv] at h1
        have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
        exact absurd h1 (not_lt.2 ((one_le_inv₀ hpos).2 hx))
  · rintro ⟨y, rfl⟩
    exact hi y

end Emb

structure CEmb (G : GAtP p) where
  iK : G.Kf →+* ℂ_[p]
  int : ∀ x : G.O, ‖iK (algebraMap G.O G.Kf x)‖ ≤ 1

theorem CEmb.mem_iff {X : Sys p} (E : CEmb X.G) [IsFractionRing X.G.O X.G.Kf] (x : X.G.Kf) :
    E.iK x ∈ OcC p ↔ x ∈ X.intK := by
  rw [mem_OcC, norm_le_one_iff E.iK E.int]
  rfl

section Conc

variable {n : ℕ} (f : K0 p →+* ℂ_[p]) (hf : ∀ x : WW p, ‖f (algebraMap (WW p) (K0 p) x)‖ ≤ 1)
  (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

def embLC : L →+* ℂ_[p] := (iC f).comp (gL L)

include hf in
theorem embLC_int (x : OL p n L) : ‖embLC f L (algebraMap (OL p n L) L x)‖ ≤ 1 :=
  (iC_int_Cp f hf _).1 ((Oc_K L _).2 ⟨x, rfl⟩)

end Conc

end Formalism.L2.G.Pend
end
end

