module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

def stdConst (CT2 C8 p m l : ℝ) : FC where
  Ct := 401
  Cc := 2
  CT2 := CT2
  CGam := m
  Csz := m
  Cr := 1
  CTu := 25
  Cdg := 1
  C5 := 1
  full := True
  GK := ⟨m, l, l, l, l, l, l, l, l, l, l, 5, 4, 1, l⟩
  cX := ⟨1, ⟨12, 3, m⟩⟩
  P :=
    { CkLow := l, Ck6 := l, CfL := l, cLL := l⁻¹, CnW := 10, Crho := l, CDelG := l, CLw := 11 * 405, Cj0 := 405,
      Cw := l, cw := 9 / 10, CDel := l, CCount := l, Ch0r := l, Ch0k := l, Ch0N := l, Cgap := l, CetaF := 6,
      CY := l, CYL := 9, Cpde := C8, CccK := 1, CF := m }
  T := { CP := p, eP := 12, Cp := 1, Cb := l, cTO := 377, ChT := l, CbN := l }

theorem stdConst_cPre (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cPre) : c = p := by
  simpa [FC.cPre, stdConst] using h

theorem stdConst_cMid (CT2 C8 p m l c : ℝ)
    (h : c ∈ (stdConst CT2 C8 p m l).cMid (stdConst CT2 C8 p m l).P.CF) : c = m := by
  simpa [FC.cMid, stdConst] using h

theorem stdConst_cLast (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cLast) : c = l := by
  simpa [FC.cLast, stdConst] using h

theorem exists_std_large (K K0 : TransportedAlt) (CT2 C8 : ℝ) (h8 : 1 ≤ C8) :
    ∃ C : FC, Std C ∧ C.CT2 = CT2 ∧ C.P.Cpde = C8 ∧ C.Large K C.P.CF ∧ C.Large K0 C.P.CF ∧ C.GK.Nonneg := by
  obtain ⟨p, hp1, hpK, hpK0⟩ : ∃ p : ℝ, 1000 ≤ p ∧ K.pre ≤ p ∧ K0.pre ≤ p :=
    ⟨max 1000 (max K.pre K0.pre), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨m, hm1, hmK, hmK0⟩ : ∃ m : ℝ, 1 ≤ m ∧ K.mid (stdConst CT2 C8 p 0 0).cOut ≤ m ∧
      K0.mid (stdConst CT2 C8 p 0 0).cOut ≤ m :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨l, hl1, hlK, hlK0⟩ : ∃ l : ℝ, 1 ≤ l ∧
      K.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l ∧
      K0.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  refine ⟨stdConst CT2 C8 p m l, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h8, hp1, ?_, ?_⟩,
    rfl, rfl, ⟨?_, trivial, ?_, ?_⟩, ⟨?_, trivial, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl⟩
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hm1
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hl1
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK0
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK0
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK0
  · exact ⟨hm0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, by norm_num [stdConst], by norm_num [stdConst],
      by norm_num [stdConst], hl0⟩

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TameVal

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : v.valuation L (x : L) ≠ 0 := by simp
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hxy
  have h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1 := by
    have := Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)
    rwa [add_sub_cancel] at this
  have h3 : χ.locK v (y * x⁻¹) = 1 := by
    refine h (atFin v (y * x⁻¹)) ?_ ?_
    · exact (hval _).trans h2
    · have : ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
          algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, hval]
      simpa using h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h3

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

theorem locK_mem (χ : HChar L) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (htame : ∀ v, χ.TameAt v) (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : χ.locK P x ∈ G := by
  classical
  have hpr : χ.ProductRule := GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩
  have key : ∀ (a : 𝓞 L) (ha : (a : L) ≠ 0), χ.locK P (Units.mk0 (a : L) ha) ∈ G := by
    intro a ha
    have ha' : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1)
      (fun v => by split_ifs; exacts [ha', one_ne_zero])
    have hP := hy P (Finset.mem_insert_self _ _)
    simp only [if_true] at hP
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hP
      have hpos : 0 < P.valuation L (a : L) := zero_lt_iff.2 (by simpa using ha')
      have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
      rw [one_mul] at this
      exact absurd hP (not_le.2 this)
    have e1 : χ.locK P (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (a : L) ha) :=
      locK_eq_of_tame χ (htame P) _ _ hP
    have e2 : ∏ v ∈ insert P T, χ.locK v (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (y : L) hy0) := by
      refine Finset.prod_eq_single P (fun v hv hne => ?_) (fun h => absurd (Finset.mem_insert_self _ _) h)
      have h1 := hy v hv
      simp only [if_neg hne] at h1
      rw [locK_eq_of_tame χ (htame v) 1 _ (by simpa using h1), map_one]
    have h := hpr (insert P T) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (Units.mk0 (y : L) hy0)
    rw [e2, e1] at h
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ insert P T),
        χ.val v ^ ordF v (Units.mk0 (y : L) hy0)) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 : _ ∈ G := h ▸ G.one_mem
    rw [G.mul_mem_cancel_right hF, G.mul_mem_cancel_left (hinf _)] at h1
    exact h1
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 L) (x : L)
  have hb0 : (b : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have ha0 : (a : L) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab]
    change (a : L) / _ = 0
    rw [h, zero_div]
  have hx : x = Units.mk0 (a : L) ha0 * (Units.mk0 (b : L) hb0)⁻¹ := by
    apply Units.ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0) (G.inv_mem (key b hb0))

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun ha hb => M.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]; exact M.inv_mem ha

theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
  have h2 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_ofNat, div_pow, ← h1]
  field_simp

end GlobalTheory.TameVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoicePolynomialLeBaseSize
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

open NumberField in
private theorem exists_mul_pow_le_exp_half_rpow (eps K : ℝ) (N : ℕ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → K * x ^ N ≤ Real.exp (x ^ eps / 2) := by
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps ((N : ℝ) + 1) 0 (1 / 2) 0 le_rfl heps (by norm_num)
  refine ⟨max (max x1 K) 1, fun x hx => ?_⟩
  have hxK : K ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1' : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hlog := hx1 x hx1'
  simp only [zero_mul, add_zero] at hlog
  calc K * x ^ N ≤ x * x ^ N := mul_le_mul_of_nonneg_right hxK (by positivity)
    _ = Real.exp (((N : ℝ) + 1) * Real.log x) := by
        rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul, Real.exp_log hxpos]
        ring
    _ ≤ Real.exp (x ^ eps / 2) := by
        apply Real.exp_le_exp.mpr
        linarith

open NumberField in
private theorem zBase_and_log_b_bounds {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (hR : _root_.GlobalTheory.EX.RankVal L.sc D.R) :
    1 ≤ L.sc.x ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.m : ℝ) ≤ 2 * L.sc.x ^ 5 ∧
      (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.r : ℝ) ≤ 4 * L.sc.x ^ 5 ∧
      ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 ∧
      Real.log L.sc.b ≤ L.sc.x ∧ 0 ≤ Real.log L.sc.b ∧
      0 ≤ _root_.Formalism.BasicNotions.zBase L ∧ _root_.Formalism.BasicNotions.zBase L ≤ 8 * L.sc.x ^ 11 ∧
      ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ 32 * L.sc.x ^ 15 := by
  obtain ⟨-, -, ⟨-, hk⟩, -⟩ := hR
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have heps := L.sc.eps_pos
  have heps' := L.sc.eps_lt
  have hx5 : x ^ (9 / 2 + 10 * L.sc.eps) ≤ x ^ 5 := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast; linarith
  have hkx : (D.R.k : ℝ) ≤ 2 * x ^ 5 := by linarith
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by
    show D.R.k + D.R.m - 1 ≤ 2 * D.R.k
    omega
  have hmx : (D.R.m : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hmk) hkx
  have hfx : (D.R.f : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hfk) hkx
  have hrx : (D.R.r : ℝ) ≤ 4 * x ^ 5 := by
    have : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
    linarith
  have hL0 : 0 ≤ L.sc.L := Real.rpow_nonneg hx0 _
  have hLx : L.sc.L ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by linarith)
    simpa [_root_.Formalism.BasicNotions.Scale.L] using h
  have hlogb : Real.log L.sc.b = L.sc.L := by simp [_root_.Formalism.BasicNotions.Scale.b]
  have hxp : 1 ≤ x ^ 377 := one_le_pow₀ hx1
  have hT : ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * x ^ 377 := by
    simp only [_root_.GlobalTheory.EX.TOv]
    have hpow : x ^ (377 : ℝ) = x ^ (377 : ℕ) := by exact_mod_cast Real.rpow_natCast x 377
    rw [hpow]
    have := Nat.ceil_lt_add_one (show 0 ≤ x ^ 377 by positivity)
    linarith
  have hz : _root_.Formalism.BasicNotions.zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L := by simp [_root_.Formalism.BasicNotions.zBase]
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hch : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
    rw [Nat.choose_two_right]
    calc D.R.r * (D.R.r - 1) / 2 ≤ D.R.r * (D.R.r - 1) := Nat.div_le_self _ _
      _ ≤ D.R.r * D.R.r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = D.R.r ^ 2 := by ring
  have hchR : ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hch
  refine ⟨hx1, hkx, hmx, hfx, hrx, hT, by rw [hlogb]; exact hLx, by rw [hlogb]; exact hL0,
    by rw [hz]; positivity, ?_, ?_⟩
  · rw [hz]
    calc (D.R.f : ℝ) * D.R.r * L.sc.L ≤ (2 * x ^ 5) * (4 * x ^ 5) * x := by gcongr
      _ = 8 * x ^ 11 := by ring
  · push_cast
    calc (D.R.f : ℝ) * ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (2 * x ^ 5) * (4 * x ^ 5) ^ 2 := by
          gcongr
          exact le_trans hchR (by gcongr)
      _ = 32 * x ^ 15 := by ring

open NumberField in
private theorem scale_b_rpow_half (s : _root_.Formalism.BasicNotions.Scale) :
    s.b ^ (1 / 2 : ℝ) = Real.exp (s.x ^ s.eps / 2) := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  rw [← Real.exp_mul]
  ring_nf

open NumberField in
private theorem exp_half_le_scale_b (s : _root_.Formalism.BasicNotions.Scale) :
    Real.exp (s.x ^ s.eps / 2) ≤ s.b := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ s.x ^ s.eps := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  linarith


open NumberField in
theorem _root_.GlobalTheory.EX.szRow_poly_le_b : _root_.GlobalTheory.EX.SzRow (fun C D L => (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ (C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ C.T.eP) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 ≤ L.sc.b)) := by
  intro eps heps _ C hC
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1 + ⌈C.T.Cb⌉₊) heps
  obtain ⟨x2, h2⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1) heps
  obtain ⟨x3, h3⟩ := exists_mul_pow_le_exp_half_rpow eps
    (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) (15 + 264 + 45) heps
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 x2) x3, fun D L hε hx hL => ?_⟩⟩⟩
  obtain ⟨hx1, hk, hm, hf, hr, hT, hlog, hlog0, hz0, hz, hQ⟩ :=
    zBase_and_log_b_bounds L hL.ranks
  have hxCb : L.sc.x ^ C.T.Cb ≤ L.sc.x ^ ⌈C.T.Cb⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have hxCb0 : 0 ≤ L.sc.x ^ C.T.Cb := Real.rpow_nonneg (by linarith) _
  have hb2 : L.sc.b ^ (1 / 2 : ℝ) = Real.exp (L.sc.x ^ eps / 2) := by rw [scale_b_rpow_half, hε]
  have hbb : Real.exp (L.sc.x ^ eps / 2) ≤ L.sc.b := hε ▸ exp_half_le_scale_b L.sc
  have hzP : _root_.Formalism.BasicNotions.zBase L ^ C.T.eP = _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ) := by
    rw [heP]; exact_mod_cast Real.rpow_natCast _ 12
  have hx0 : (0 : ℝ) ≤ L.sc.x := by linarith
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  refine ⟨?_, ?_, ?_⟩
  · calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x * L.sc.x ^ ⌈C.T.Cb⌉₊ := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1 + ⌈C.T.Cb⌉₊) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h1 _ hxa
      _ ≤ L.sc.b := hbb
  · rw [hb2]
    calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h2 _ hxb
  · rw [hzP]
    have hrest : 0 ≤ (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
        ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 := by positivity
    calc C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3
          = C.T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := by ring
      _ ≤ |C.T.CbN| * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hrest
      _ ≤ |C.T.CbN| * ((4 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) *
            (C.T.CP * (8 * L.sc.x ^ 11) ^ (12 : ℕ)) ^ 2 * (32 * L.sc.x ^ 15) ^ 3) := by gcongr
      _ = (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) * L.sc.x ^ (15 + 264 + 45) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h3 _ hxc
      _ ≤ L.sc.b := hbb

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRankKLowerUpperBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem rank_k_ineqs_poly_wide (C w y n m k : ℝ) (hw : 0 < w) (hy : 128 * |C| + 2 ≤ y)
    (hn1 : w ^ 4 * y ^ 128 ≤ n) (hn2 : n ≤ 2 * (w ^ 4 * y ^ 129))
    (hm1 : w / y ≤ m) (hm2 : m ≤ 2 * (w / y))
    (hk1 : w ^ 9 * y ^ 160 ≤ k) (hk2 : k ≤ 2 * (w ^ 9 * y ^ 160)) :
    C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16 ≤ k ∧ k ≤ w * n * (n * (y ^ 16)⁻¹) ∧
      Real.sqrt (k / m) ≤ n * (y ^ 16)⁻¹ := by
  have hC := abs_nonneg C
  have hy2 : 2 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn1
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hR : w ^ 4 * y ^ 112 ≤ n * (y ^ 16)⁻¹ := by
    calc w ^ 4 * y ^ 112 = (w ^ 4 * y ^ 128) * (y ^ 16)⁻¹ := by field_simp
      _ ≤ n * (y ^ 16)⁻¹ := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · have h5 : 128 * |C| ≤ y ^ 4 := by
      calc 128 * |C| ≤ y := by linarith
        _ ≤ y ^ 4 := le_self_pow₀ hy1 (by norm_num)
    calc C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16
        ≤ |C| * (2 * (w / y)) ^ 5 * (2 * (2 * (w ^ 4 * y ^ 129))) * y ^ 16 * y ^ 16 := by
          gcongr
          exact le_abs_self C
      _ = (128 * |C|) * (w ^ 9 * y ^ 156) := by field_simp; ring
      _ ≤ y ^ 4 * (w ^ 9 * y ^ 156) := by gcongr
      _ = w ^ 9 * y ^ 160 := by ring
      _ ≤ k := hk1
  · have h80 : 2 ≤ y ^ 80 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    calc k ≤ 2 * (w ^ 9 * y ^ 160) := hk2
      _ ≤ y ^ 80 * (w ^ 9 * y ^ 160) := by gcongr
      _ = w * (w ^ 4 * y ^ 128) * (w ^ 4 * y ^ 112) := by ring
      _ ≤ w * n * (n * (y ^ 16)⁻¹) := by gcongr
  · have h63 : 2 ≤ y ^ 63 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    refine le_trans ?_ hR
    rw [Real.sqrt_le_left (by positivity)]
    have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
    calc k / m ≤ (2 * (w ^ 9 * y ^ 160)) / (w / y) := by gcongr
      _ = 2 * (w ^ 8 * y ^ 161) := by field_simp
      _ ≤ y ^ 63 * (w ^ 8 * y ^ 161) := by gcongr
      _ = (w ^ 4 * y ^ 112) ^ 2 := by ring

theorem explicitChoice_rankK_lower_upper_bounds :
    SzRow (fun C D L => (C.P.CkLow * (D.R.m : ℝ) ^ jG * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k) ∧
      ((D.R.k : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) * D.R.n * R0 L) ∧ (Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ R0 L)) := by
  intro eps he _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (eps / 16)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (128 * |C.P.CkLow| + 2))
  refine ⟨x0, fun D L hε hx hV => ?_⟩
  have hn2 : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) := by
    have h1 : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])
    linarith [hV.ranks.n_le]
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  have hy := hx0 _ hx
  rw [← hε] at hy
  have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have key : ∀ (a b : ℕ), (L.sc.x ^ ((1 : ℝ) / 2)) ^ a * (L.sc.x ^ (L.sc.eps / 16)) ^ b =
      L.sc.x ^ ((a : ℝ) / 2 + b * L.sc.eps / 16) := by
    intro a b
    rw [← Real.rpow_mul_natCast hxp.le, ← Real.rpow_mul_natCast hxp.le, ← Real.rpow_add hxp]
    congr 1; ring
  have e1 : L.sc.x ^ (2 + 8 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 128 := by
    rw [key]; congr 1; push_cast; ring
  have e1' : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) =
      (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 129 := by
    rw [key]; congr 1; push_cast; ring
  have e2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 9 * (L.sc.x ^ (L.sc.eps / 16)) ^ 160 := by
    rw [key]; congr 1; push_cast; ring
  have e3 : L.sc.x ^ L.sc.eps = (L.sc.x ^ (L.sc.eps / 16)) ^ 16 := by
    rw [← Real.rpow_mul_natCast hxp.le]; congr 1; push_cast; ring
  have e4 : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 : ℝ) / 2) / L.sc.x ^ (L.sc.eps / 16) := by
    unfold Scale.delta1
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hxp.le (by positivity), ← Real.rpow_mul hxp.le, div_eq_mul_inv (_ ^ _),
      ← Real.rpow_neg hxp.le]
    congr 2; ring
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Ranks.f; push_cast; rfl
  rw [e1] at hn1
  rw [e1'] at hn2
  rw [e2] at hk1 hk2
  rw [e4] at hm1 hm2
  have h := rank_k_ineqs_poly_wide C.P.CkLow _ _ _ _ _ (by positivity) hy hn1 hn2 hm1 hm2 hk1 hk2
  simp only [R0, jG, Scale.L, hf, Real.rpow_neg hxp.le, e3]
  exact h

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSum
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem isExt_KT : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  intro D u X i M M' K φ Φ hK hΦ
  refine ⟨fun c' => ?_, fun g' p' => ?_⟩
  · show Formalism.ThetaLiftIndependence.kerOpM (X.C.wt i) (X.C.Kmap i) φ c' = _
    unfold Formalism.ThetaLiftIndependence.kerOpM
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΦ.1 c, K.Kmap_eq, Submodule.coe_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hK g']

end GlobalTheory.LvT
end

