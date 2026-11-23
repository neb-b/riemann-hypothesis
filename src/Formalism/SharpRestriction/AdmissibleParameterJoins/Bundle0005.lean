module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSt
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Mathlib
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLi
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

theorem mEatT_nat (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ∃ n : ℕ, (D.R.m : ℝ) * EatT D u w = n := by
  classical
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := D.R.t_odd
  have hm : (D.R.m : ℝ) = 2 * (a : ℝ) := by rw [ha]; push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * (b : ℝ) + 1 := by rw [hb]; push_cast; ring
  unfold EatT
  split_ifs with hs
  · first
    | simp only [Formalism.MainNotions.G.Nm]
    | simp only [Formalism.Nm]
    | skip
    refine ⟨D.R.m * (2 * ∑ τ : D.what₂.Tau, Wtau D u τ) + D.R.m * D.R.f * D.R.N D.R.m +
      (topsOf D.host D.eTau).card * (b + 1) * a * (2 * a + 1), ?_⟩
    push_cast
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

theorem vAdd_Tpow (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (n : ℕ) :
    D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n) = (((n * D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_pow, ← hw, D.what₂.places.val_resChar w, ← WithTop.coe_nsmul]
  congr 1

theorem ColGe0_atT (D : D7) (u : D.what₂.Word) (h5 : Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) (x : ((D.fm u).lat 0).V) (hx : x ∈ LT.Nlam D u w) :
    ColGe0 D u w x (-((D.R.m : ℝ) * EatT D u w)) := by
  obtain ⟨n0, hn0⟩ := mEatT_nat D u w
  have hT0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ≠ 0 := by
    have hp := D.what₂.places.resChar_prime w
    rw [hw] at hp
    exact_mod_cast hp.ne_zero
  have hc0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ≠ 0 := pow_ne_zero _ hT0
  have hval := vAdd_Tpow D u w hw n0
  have hle : (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * Formalism.MainNotions.product_first_zeroth_parts.ET D u w) ≤
      (((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℝ) := by
    show (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ _
    rw [hn0]
    push_cast
    rw [mul_comm]
  obtain ⟨y', hy'S, hy'⟩ := h5 w hw _ _ hval hle x hx
  refine ⟨((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ • y', ?_,
    ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹, y', hy'S, rfl, Or.inr ?_⟩
  · rw [map_smulₛₗ, hy', smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
    rfl
  · have hinv : D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        ((-((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
      rw [AddValuation.map_inv, hval]
      rfl
    have hv := D.val_eq w _ (inv_ne_zero hc0)
    rw [hinv] at hv
    have hvz : vAdd (D.plEq w) ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        -((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) := (WithTop.coe_injective hv).symm
    rw [hvz]
    show (D.what₂.places.ramIdx w : ℝ) * (-((D.R.m : ℝ) * EatT D u w)) ≤ _
    rw [hn0]
    push_cast
    nlinarith

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSu
section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Be

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem lg_pt (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hax : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hae : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply hae hax, hinv, PowerSeries.subst_X hax]

variable (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p])

theorem be_at (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {a b : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst ![C ep * g.lg a, C ep * g.lg b] (map i0 be) = g.be a b := by
  have hlg : ∀ {σ' : Type} {c : σ' → MvPowerSeries τ ℂ_[p]}, HasSubst c → ∀ i : σ',
      subst c (C ep * g.lg (X i)) = C ep * g.lg (c i) := by
    intro σ' c hc i
    have hXi : HasSubst (fun _ : Unit => (X i : MvPowerSeries σ' ℂ_[p])) := by
      have hz : ∀ _ : Unit, constantCoeff (X i : MvPowerSeries σ' ℂ_[p]) = 0 := fun _ => constantCoeff_X i
      first
        | exact hasSubst_of_constantCoeff_zero hz
        | exact HasSubst.of_constantCoeff_zero' hz
        | exact hasSubst_of_constantCoeff_nilpotent (fun j => by rw [hz j]; exact IsNilpotent.zero)
    rw [← smul_eq_C_mul, subst_smul hc, ← smul_eq_C_mul]
    congr 1
    unfold G1.lg PowerSeries.subst
    rw [subst_comp_subst_apply hXi hc]
    simp only [subst_X hc]
  have h0 : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hc : HasSubst ![a, b] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have hl0 : ∀ i : Fin 2, constantCoeff (g.lg (X i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ (cc_l g)
  have h1 : ∀ i : Fin 2, constantCoeff
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i) = 0 := by
    intro i; fin_cases i <;> simp [hl0]
  have hd : HasSubst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] := by
    first
      | exact hasSubst_of_constantCoeff_zero h1
      | exact HasSubst.of_constantCoeff_zero' h1
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h1 i]; exact IsNilpotent.zero)
  have h := congrArg (subst ![a, b]) be_tie
  rw [be_subst g hex hc (constantCoeff_X _) (constantCoeff_X _), subst_X hc, subst_X hc,
    subst_comp_subst_apply hd hc] at h
  have hfun : (fun i => subst ![a, b]
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i)) = ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hlg hc 0
    · exact hlg hc 1
  rw [hfun] at h
  simpa using h

def LogOf (x : MvPowerSeries τ (K0 p)) (a : MvPowerSeries τ ℂ_[p]) : Prop :=
  constantCoeff x = 0 ∧ constantCoeff a = 0 ∧
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 x) = C ep * g.lg a

theorem logOf_X (i : τ) : LogOf g i0 ep (X i) (X i) := by
  refine ⟨constantCoeff_X i, constantCoeff_X i, ?_⟩
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  rw [map_X, subst_X (hs_dg hc), dg_Cmul]

theorem logOf_add (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) : LogOf g i0 ep (x + y) (g.add a b) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hlb : constantCoeff (g.lg b) = 0 := PowerSeries.constantCoeff_subst_eq_zero hb0 _ (cc_l g)
  have hs : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add (f := _), hla, hlb, add_zero]
  refine ⟨by rw [map_add (f := _), hx0, hy0, add_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_add (f := _), subst_add (hs_dg hc), hx1, hy1, G1.add, lg_pt g hex hinv hs, mul_add]

theorem logOf_mul (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) (c : K0 p) {x : MvPowerSeries τ (K0 p)}
    {a : MvPowerSeries τ ℂ_[p]} (hx : LogOf g i0 ep x a) : LogOf g i0 ep (C c * x) (g.mulBy (i0 c) a) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hs : constantCoeff (C (i0 c) * g.lg a) = 0 := by rw [map_mul, hla, mul_zero]
  refine ⟨by rw [map_mul, hx0, mul_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_mul, map_C, ← smul_eq_C_mul, subst_smul (hs_dg hc), hx1, G1.mulBy, lg_pt g hex hinv hs,
      smul_eq_C_mul]
    ring

theorem subtraction_formal_group_log (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) :
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 (sub2 p be x y)) = g.be a b := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have h0' : ∀ i : Fin 2, constantCoeff (map i0 (![x, y] i)) = 0 := by
    intro i; rw [constantCoeff_map, h0 i, map_zero]
  have hs' : HasSubst (fun i : Fin 2 => map i0 (![x, y] i)) := by
    first
      | exact hasSubst_of_constantCoeff_zero h0'
      | exact HasSubst.of_constantCoeff_zero' h0'
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0' i]; exact IsNilpotent.zero)
  unfold sub2
  rw [map_subst hs, subst_comp_subst_apply hs' (hs_dg hc)]
  have hfun : (fun i : Fin 2 => subst (diagS (PowerSeries.C ep * g.l)) (map i0 (![x, y] i))) =
      ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hx1
    · exact hy1
  rw [hfun]
  exact be_at g i0 be ep hex be_tie ha0 hb0

theorem constantCoeff_sub2_eq_zero (hbe : constantCoeff be = 0) {x y : MvPowerSeries τ (K0 p)} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (sub2 p be x y) = 0 := by
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact Formalism.G.LogP.hs2 hx hy
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  unfold sub2
  first
    | exact constantCoeff_subst_eq_zero hs h0 hbe
    | exact constantCoeff_subst_eq_zero h0 hbe
    | exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 hbe

end Be

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.LenAtT
section
namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem lenAtT (D : D7) (L : SizeData₂ D) (hAtT : NuAtTDef D L) : LenAtT D L :=
  fun u w hw => D.lenLoc_atT hAtT u w hw

theorem locSpan (D : D7) : LocSpan D := fun u w y hy => D.locSpan u w y hy

end Formalism.MainNotions.J
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLq
section
noncomputable section

namespace Formalism.MainNotions.J

open Finset NumberField IsDedekindDomain Formalism.BasicNotions

theorem card_GL_real (g n : ℕ) [Fact g.Prime] :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = LocalBesselAndTopKernel.cardGL (g : ℝ) n := by
  rw [Matrix.card_GL_field, ZMod.card]
  unfold LocalBesselAndTopKernel.cardGL
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((g ^ n - g ^ i : ℕ) : ℝ)) n]
  refine prod_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos (le_of_lt (mem_range.mp hi)))]
  push_cast
  rfl

theorem cardGL_factor (q : ℝ) (k : ℕ) :
    LocalBesselAndTopKernel.cardGL q k = q ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1) := by
  unfold LocalBesselAndTopKernel.cardGL
  have h1 : ∀ i ∈ range k, q ^ k - q ^ i = q ^ i * (q ^ (k - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := mem_range.mp hi
    have : k = i + (k - 1 - i + 1) := by omega
    conv_lhs => rw [this, pow_add]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id,
    prod_range_reflect (fun j => q ^ (j + 1) - 1) k]
  congr 1
  rw [range_eq_Ico, prod_Ico_add' (fun j => q ^ j - 1) 0 k 1]
  refine prod_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

theorem idxColLoc_eq (g k : ℕ) [Fact g.Prime] :
    StandardLattice.idxColLoc g k = ∏ i ∈ Finset.Icc 1 k, ((g : ℝ) ^ i - 1) := by
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  have hc : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      g ^ (k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin k) (ZMod g) =>
      isUnitri_iff (A : Matrix (Fin k) (Fin k) (ZMod g))), card_pat _ (by simp [upS]), card_upS, Nat.card_zmod]
  have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  rw [card_GL_real, hc, cardGL_factor, Nat.cast_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hg)]

theorem dim_arith (k r c : ℕ) (h : c + k = (k + 2 * r + 1) * (k + 2 * r + 1 - 1) / 2) :
    c = r * (2 * k + 2 * r + 1) + k * (k - 1) / 2 := by
  rcases k with _ | k
  · have e : (0 + 2 * r + 1) * (0 + 2 * r + 1 - 1) = 2 * (r * (2 * 0 + 2 * r + 1)) + 0 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega
  · have e : (k + 1 + 2 * r + 1) * (k + 1 + 2 * r + 1 - 1) =
        2 * (r * (2 * (k + 1) + 2 * r + 1) + (k + 1)) + (k + 1) * (k + 1 - 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega

theorem idxRowLoc_eq (g k m : ℕ) [Fact g.Prime] (hm : Even m) (h2 : 2 ≤ m) :
    StandardLattice.idxRowLoc g k m = LocalBesselAndTopKernel.cardGL (g : ℝ) (k + m - 1) /
      ((g : ℝ) ^ ((m / 2 - 1) * (2 * k + 2 * (m / 2 - 1) + 1)) * (g : ℝ) ^ (k * (k - 1) / 2)) := by
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  obtain ⟨a, rfl⟩ := hm
  have ha : (a + a) / 2 - 1 = a - 1 := by omega
  have hn : k + (a + a) - 1 = k + 2 * (a - 1) + 1 := by omega
  have hc : Nat.card {A : GL (Fin (k + (a + a) - 1)) (ZMod g) //
      StandardLattice.IsRowLev k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))} =
      g ^ (((a + a) / 2 - 1) * (2 * k + 2 * ((a + a) / 2 - 1) + 1) + k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin (k + (a + a) - 1)) (ZMod g) =>
      isRowLev_iff k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))),
      card_pat _ (by simp only [rowS, upS, mem_filter, mem_univ, true_and]; exact fun p hp => hp.1), Nat.card_zmod]
    congr 1
    have h := card_rowS k ((a + a) / 2 - 1) (k + (a + a) - 1) (by omega)
    rw [ha] at h ⊢
    rw [hn] at h ⊢
    exact dim_arith k (a - 1) _ h
  rw [card_GL_real, hc, Nat.cast_pow, pow_add]

theorem finprod_typed (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (φ : ℕ → ℝ) :
    ∏ᶠ p ∈ S.typedPl D, φ (Ideal.absNorm p.asIdeal) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  have hf : D.R.f ≠ 0 := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hfin : ∀ i, ({p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}).Finite := by
    intro i
    have hc := (h i).1
    have hF : Finite {p : HeightOneSpectrum (𝓞 D.host.F) // ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact hf)
    exact Set.finite_coe_iff.mp hF
  have hone : ∀ i, ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal) = φ (D.host.g i) ^ D.R.f := by
    intro i
    have e : ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
        φ (Ideal.absNorm p.asIdeal) =
        ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
          φ (D.host.g i) :=
      finprod_mem_congr rfl fun p hp => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, (h i).2 p hp]
    rw [e, finprod_mem_eq_finite_toFinset_prod _ (hfin i), Finset.prod_const,
      ← Set.ncard_eq_toFinset_card _ (hfin i), ← Nat.card_coe_set_eq]
    exact congrArg _ (h i).1
  have hdis : Disjoint {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := by
    refine Set.disjoint_left.mpr fun p h0 h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (a : 𝓞 D.host.F) * ((D.host.g 0 : ℕ) : 𝓞 D.host.F) + (b : 𝓞 D.host.F) * ((D.host.g 1 : ℕ) : 𝓞 D.host.F) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.F) hab
    rw [← hab']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hU : S.typedPl D = {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} ∪
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := rfl
  rw [hU, finprod_mem_union hdis (hfin 0) (hfin 1), hone 0, hone 1]

theorem idxColTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxColTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxColTie StandardLattice.idxPi S.gaG
  rw [finprod_typed D h (fun N => ∏ i ∈ Finset.Icc 1 D.R.k, ((N : ℝ) ^ i - 1)), idxColLoc_eq, idxColLoc_eq]

theorem idxRowTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxRowTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxRowTie StandardLattice.idxSig LocalBesselAndTopKernel.idxRows
  rw [finprod_typed D h (fun N => LocalBesselAndTopKernel.cardGL (N : ℝ) D.R.r /
    ((N : ℝ) ^ LocalBesselAndTopKernel.dimNS D * (N : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))),
    idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m, idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m]
  rfl

end Formalism.MainNotions.J

end
end

