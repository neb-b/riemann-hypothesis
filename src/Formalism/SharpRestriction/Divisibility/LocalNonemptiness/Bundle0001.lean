module

public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalRingCardinality.HostCls

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
section
noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions




private theorem eventually_abs_le_half_add_of_doubling_bounds (x y w : ℚ) (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z + 1 / 2)
    (hw : ∃ z : ℤ, w = z) (h1 : x < y) (h2 : y < w) : x + 1 ≤ w := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hw
  have h1' : (a : ℚ) < ((b + 1 : ℤ) : ℚ) := by push_cast; linarith
  have h2' : (b : ℚ) < (c : ℚ) := by linarith
  have h1'' : a < b + 1 := by exact_mod_cast h1'
  have h2'' : b < c := by exact_mod_cast h2'
  have h3 : a + 1 ≤ c := by omega
  exact_mod_cast h3

theorem sigPar_step (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) + 1 ≤ DV.sigPar D τ i := by
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    exact eventually_abs_le_half_add_of_doubling_bounds ((D.hc τ).v ⟨i + 1, h1⟩) ((D.hc τ).u ⟨i + 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
      ((D.hc τ).v_int ⟨i + 1, h1⟩) ((D.hc τ).u_half ⟨i + 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
      ((D.hc τ).u_gt_v ⟨i + 1, h1⟩) ((D.hc τ).v_gt_u ⟨i, h0⟩)
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hk : 0 < D.R.k := by omega
      have hm : 0 < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb, dif_pos h0]
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, hm⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = 0 by omega)
      rw [e1]
      have hu2 : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        have h5 := (D.hc τ).v_gt_u ⟨i, h0⟩
        have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨i + 1, by omega⟩ :=
          Fin.ext (show D.R.k - 1 = i + 1 by omega)
        rw [e2]
        exact h5
      obtain ⟨zb, hzb⟩ := (D.hc τ).b_int ⟨0, hm⟩
      exact eventually_abs_le_half_add_of_doubling_bounds (-(D.hc τ).b ⟨0, hm⟩) ((D.hc τ).u ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
        ⟨-zb, by rw [hzb, Int.cast_neg]⟩ ((D.hc τ).u_half ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
        ((D.hc τ).u_last_gt hk hm) hu2
    · have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb1, dif_neg h0, dif_pos hb0]
      have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have g2 : ((D.R.t : ℚ) + 3) / 2 ≤
          (D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ - (D.hc τ).e ⟨i - (D.R.k - 1), hb0⟩ :=
        (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (show i - (D.R.k - 1) + 1 < D.R.m by omega)
      have e : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 by omega)
      rw [e]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  have h := sigPar_step D τ i hi
  unfold DV.aPlusQ
  push_cast
  linarith

theorem aPlusQ_anti (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : b < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ b ≤ DV.aPlusQ D j τ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (aPlusQ_step D j τ (a + d) (by omega)).trans (ih (by omega))

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + (c + 1) < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dif_pos h0, dif_pos hc]
  have g1 := (D.hc τ).gap_be ⟨j + c, h0⟩
  have g2 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j + (c + 1), hc⟩ - (D.hc τ).e ⟨j + c, h0⟩ :=
    (D.hc τ).gap_eb ⟨j + c, h0⟩ (show j + c + 1 < D.R.m by omega)
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : j + b < D.R.m) :
    DV.aMinusQ D j τ a ≤ DV.aMinusQ D j τ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega)).trans (aMinusQ_step D j τ (a + d) (by omega))

end Formalism.MainNotions.DIV.Inh

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
section
noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

theorem even_add_order_two_le (D : D7) (h : HH D) (hev : Even (addOrderOf h)) : Even (addOrderOf h) ∧ 2 ≤ addOrderOf h := by
  have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
  refine ⟨hev, ?_⟩
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  obtain ⟨k, hk⟩ := hev
  omega

theorem orbOK_iff (D : D7) (p : ℕ) : OrbOK D p ↔ 5 ≤ p ∧ (IsSg D p ∨ HEv D p) := by
  constructor
  · rintro ⟨h5, hev, -⟩
    refine ⟨h5, ?_⟩
    by_cases hs : IsSg D p
    · exact Or.inl hs
    · right
      unfold nP at hev
      rw [if_neg hs] at hev
      exact hev
  · rintro ⟨h5, hc⟩
    by_cases hs : IsSg D p
    · have hpos : 0 < addOrderOf (2 • hP D p) := by
        have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
        exact addOrderOf_pos _
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_pos hs]
        exact even_two_mul _
      · unfold nP
        rw [if_pos hs]
        omega
    · have hev : HEv D p := hc.resolve_left hs
      obtain ⟨h1, h2⟩ := even_add_order_two_le D (hP D p) hev
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_neg hs]
        exact h1
      · unfold nP
        rw [if_neg hs]
        exact h2

private theorem five_le_of_prime_not_small_not_split (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hs : p ∉ D.host.toHostRaw.small) (hj : ¬ jacobiSym (-(D.host.d : ℤ)) p = 1) : 5 ≤ p := by
  by_contra hlt
  have h2 : 2 ≤ p := hp.two_le
  have hne2 : p ≠ 2 := by
    rintro rfl
    apply hs
    have hm : 2 ∈ D.host.toHostRaw.QS.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) D.host.tower_dvd,
        D.host.QS_pos.ne'⟩
    exact hm
  have hne4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  obtain rfl : p = 3 := by omega
  exact hj (D.host.split_small 3 hp (by norm_num) h3)

theorem five_le_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound) (hc : IsResidueClassZero D p ∨ IsSg D p) : 5 ≤ p := by
  have hcls : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal := hc
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass at hcls
  split_ifs at hcls with a1 a2 a3 a4 a5 <;>
    first
      | exact five_le_of_prime_not_small_not_split D p hp h3 a1 a4
      | simp at hcls

theorem orbOK_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hc : (IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) : OrbOK D p := (orbOK_iff D p).2 ⟨five_le_of_class D p hp h3 (hc.imp And.left id), hc.elim (fun h => Or.inr h.2) Or.inl⟩

theorem orbit_admissible_of_split_bound (D : D7) (h3 : 3 ≤ D.host.splitBound) : OrbitParityCond D := by
  unfold OrbitParityCond
  exact ⟨fun p hp hc => orbOK_of_class D p hp h3 hc, fun p hp hc => five_le_of_class D p hp h3 (Or.inl hc)⟩

section Shape

variable {D : D7}

variable {L : SizeData₂ D} {X : Inst D L}

end Shape

end Formalism.MainNotions.DIV.Inh

end
end

