module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlVolEqTsumSlabVol
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberRootDiscFactorLeHHZ
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SizeQ

theorem one_le_size (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun τ _ => ?_)
  exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun l _ => le_max_left _ _)

private lemma one_add_logb_two_mul_le_of_log_le_sqrt (f r : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hlog : Real.log f ≤ Real.sqrt r) : 1 + Real.logb 2 (2 * (f : ℝ)) ≤ 2 * (r : ℝ) + 2 := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsq : Real.sqrt r ≤ r := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsplit : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.log f / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hf0.ne', add_div, div_self (by linarith)]
  have hdiv : Real.log f / Real.log 2 ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem classNumber_le (D : D7) (b : ℝ) (hb : 1 ≤ b) (hrd : D.host.rdE ≤ b) (hf : 1 ≤ D.R.f)
    (hr : 1 ≤ D.R.rS) (hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS) :
    (classNumber D.host.E : ℝ) ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
  obtain ⟨-, hdeg, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D
  have hcn := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.classNumberBound D.host.E
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hdeg' : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by rw [hdeg]; push_cast; ring

  have hdisc : |(NumberField.discr D.host.E : ℝ)| = D.host.rdE ^ (2 * (D.R.f : ℝ)) := by
    rw [Formalism.BasicNotions.Host.rdE, hdeg', ← Real.rpow_mul (abs_nonneg _), one_div,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [hdisc, hdeg', ← Real.rpow_mul (by linarith)] at hcn
  have hc := one_add_logb_two_mul_le_of_log_le_sqrt D.R.f D.R.rS hf hr hlog
  have hf1r : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hlb : 0 ≤ Real.logb 2 (2 * (D.R.f : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  calc (classNumber D.host.E : ℝ)
      ≤ D.host.rdE ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) := hcn
    _ ≤ b ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) :=
        Real.rpow_le_rpow (by linarith) hrd (by positivity)
    _ ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        rw [hm']
        nlinarith

private lemma le_rpow_abs_div_eight_of_mul_pow_le (k b Cg g : ℝ) (hk : 0 ≤ k) (hb : 1 ≤ b) (h1 : (k * b) ^ 8 ≤ g)
    (h2 : g ≤ b ^ Cg) : k ≤ b ^ (|Cg| / 8) := by
  have hk8 : k ^ 8 ≤ b ^ |Cg| := by
    calc k ^ 8 ≤ (k * b) ^ 8 := by
          apply pow_le_pow_left₀ hk; nlinarith
      _ ≤ b ^ Cg := h1.trans h2
      _ ≤ b ^ |Cg| := Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _)
  by_contra hlt
  push_neg at hlt
  have hpos : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg (by linarith) _
  have := pow_lt_pow_left₀ hlt hpos (by norm_num : (8 : ℕ) ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at this
  norm_num at this
  linarith

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨|Cg| / 8 + 3 / 2 + 6, ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH Z
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, hmf, -, hlogf, -, -, -, -, -, hlrd, hg1, hg1b, -, -, -, -, -, hv, -, -, -, -, -, -⟩ := hS0
  have hr : 1 ≤ D.R.rS := hSt.1
  obtain ⟨-, -, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D

  set b := large₂.sc.b with hbdef
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hbexp : b = Real.exp large₂.sc.L := rfl
  have hrd2 : 2 ≤ D.host.rdE := by
    have : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hrdb : D.host.rdE ≤ b := by
    have hlog : Real.log D.host.rdE ≤ large₂.sc.L := by
      have : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self hL.le hCl
      linarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr hlog
      _ = b := hbexp.symm
  have hb2 : 2 ≤ b := hrd2.trans hrdb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm4 : 4 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf

  have hk : (D.R.k : ℝ) ≤ b ^ (|Cg| / 8) := le_rpow_abs_div_eight_of_mul_pow_le _ _ _ _ (Nat.cast_nonneg _) hb1 hg1 hg1b
  have hsq : D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hrdb (by norm_num)
  have hbase : 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ (|Cg| / 8 + 3 / 2) := by
    have e : b ^ (|Cg| / 8 + 3 / 2) = b ^ (1 : ℝ) * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, Real.rpow_one]
    have h0 : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h0' : 0 ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
    have h0'' : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg hb0.le _
    calc 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b * b ^ (|Cg| / 8) * D.host.rdE ^ ((1 : ℝ) / 2) := by
          gcongr
      _ ≤ b * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by gcongr
  have hcls := classNumber_le D b hb1 hrdb hf1 hr hlogf
  have h18 : (2 : ℝ) ^ D.R.f * 9 ^ D.R.f ≤ b ^ ((5 : ℝ) * D.R.f) := by
    rw [← mul_pow, Real.rpow_mul hb0.le, Real.rpow_natCast]
    apply pow_le_pow_left₀ (by norm_num)
    have : (2 : ℝ) ^ (5 : ℝ) ≤ b ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hb2 (by norm_num)
    have h32 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith

  set e1 : ℝ := |Cg| / 8 + 3 / 2 with he1
  have he1n : 0 ≤ e1 := by positivity
  have hpow : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f ≤ b ^ (e1 * D.R.f) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hprod : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f
      ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := by
    have e : b ^ ((e1 + D.R.m + 5) * D.R.f) = b ^ (e1 * D.R.f) * b ^ ((D.R.m : ℝ) * D.R.f) * b ^ ((5 : ℝ) * D.R.f) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, mul_assoc _ ((2 : ℝ) ^ D.R.f)]
    have hc0 : (0 : ℝ) ≤ classNumber D.host.E := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ D.R.f * 9 ^ D.R.f := by positivity
    gcongr

  have hm1 : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm4
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |Cg| / 8 := by positivity
    linarith
  have hexp : (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have h1 : e1 + D.R.m + 5 ≤ C * D.R.m := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - (e1 + 6)) (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg he1n (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
    have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : 1 ≤ C * (D.R.m : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hC1 hm2
    have h3 : e1 + D.R.m + 5 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) :=
      h1.trans (le_mul_of_one_le_left (by positivity) h2)
    calc (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) * D.R.f :=
          mul_le_mul_of_nonneg_right h3 hf0
      _ = C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by ring
  have hsz := one_le_size D b C Z
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  calc _ ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := hprod
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
        have : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hsz
        have : 0 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_nonneg hb0.le _
        nlinarith

end GlobalTheory.LoopC.SizeQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangular
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabNormal

variable {k r : ℕ}

theorem xstJ_self : XstJ k r r = Xst k r := by
  unfold XstJ Xst
  congr 1
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, a.2⟩, rfl⟩

theorem isNormal0_iff {β : Fin r → ℕ} {g : Mat k r} (z' : Fin (2 * r + k + 1) → ℂ) :
    IsNormal0 k r le_rfl β 1 (g *ᵥ z') z' g ↔ IsNormal k r β g := by
  constructor
  · rintro ⟨hg, -, -, -, -, hX, -, hB⟩
    refine ⟨hg, fun a => ?_, hB⟩
    rw [← xstJ_self]
    exact hX a a.2
  · rintro ⟨hg, hX, hB⟩
    refine ⟨hg, by simp, by simp, hB.1, fun a b hb => absurd b.2 (not_lt.2 hb), fun a _ => ?_,
      fun a ha => absurd a.2 (not_lt.2 ha), hB⟩
    rw [xstJ_self]
    exact hX a

theorem pTop_self (q : PTop k r r) : pTop k r r q = 1 := by
  have h1 : (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have h2 : (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) = 0 :=
    funext fun p => dif_neg (not_le.2 p.1.1.2)
  have h3 : (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have hs : skewM (0 : UT r → ℂ) (0 : Fin r → ℝ) = 0 := by
    ext a b
    simp only [skewM]
    split_ifs <;> simp
  show pEl k r (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0)
      (skewM (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0)
        (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) = 1
  rw [h1, h2, h3, hs]
  exact Rad.pEl_zero

theorem rEl_self (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r r) : rEl k r r β q = uEmb k r (upperIn β q.1) := by
  show uEmb k r (upperIn β q.1) * pTop k r r q.2 = _
  rw [pTop_self, mul_one]

theorem range_rEl (β : Fin r → ℕ) :
    Set.range (rEl k r r β) = Set.range fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
  ext m
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (rEl_self β q).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rEl_self β (x, 0)⟩

theorem volume_pTop : (volume : Measure (PTop k r r)) Set.univ = 1 := by
  haveI : IsEmpty {a : Fin r // r ≤ a.val} := ⟨fun a => absurd a.2 (not_le.2 a.1.2)⟩
  haveI : IsEmpty {p : UT r // r ≤ p.1.1.val} := ⟨fun p => absurd p.2 (not_le.2 p.1.1.1.2)⟩
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, ← Set.univ_prod_univ,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem lebesgueCommonStabilizerNormalForm_full_eq (β : Fin r → ℕ) : lebR0 k r r β = lebR k r β := by
  have hc : Continuous fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x)) := by
    have h := (RConj.continuous_rEl (k := k) (r := r) r β).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : UTin β → ℂ => (0 : PTop k r r)))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have := h.matrix_elem i j
    simpa [Function.comp_def, rEl_self] using this
  have hf : (fun q : (UTin β → ℂ) × PTop k r r => Matrix.of.symm (rEl k r r β q)) =
      (fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x))) ∘ Prod.fst := by
    funext q
    simp [rEl_self]
  rw [lebR0, lebR, hf, ← Measure.map_map hc.measurable measurable_fst, Measure.volume_eq_prod,
    Measure.map_fst_prod, volume_pTop, one_smul]

theorem tz_last : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by
  have hv : (wI k r (Fin.last k)).val = r + k := rfl
  have hH : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
    unfold Hpk
    rw [hv]
    simp
  have he : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, bvec, Matrix.mulVec_single, dotProduct, Pi.single_apply]
  unfold Tz
  rw [he, hH]
  norm_num

theorem stabiliser_normal : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  intro k r g₀ β hN
  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * r + k + 1) → ℂ, w = bvec (wI k r (Fin.last k)) := ⟨_, rfl⟩
  have h0 : IsNormal0 k r le_rfl β 1 (g₀ *ᵥ w) w g₀ := (isNormal0_iff w).2 hN
  have hwW : inWb k r w := hw ▸ NfMid.inWb_bvec _
  have hzW : inWb k r (g₀ *ᵥ w) := NfMid.inWb_mulVec h0 hwW
  have hT : 0 < Tz k r (g₀ *ᵥ w) := by
    rw [← NfMid.tz_eq h0, hw]
    exact tz_last
  obtain ⟨hR, hC⟩ := _root_.GlobalTheory.Amp.rset_normal0 k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  obtain ⟨hH, hU⟩ := _root_.GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  have hM := RConj.lebR0_map_conjM_eq_of_isNormalZero k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  rw [lebesgueCommonStabilizerNormalForm_full_eq] at hH hU hM
  rw [range_rEl] at hR
  refine ⟨hR, hC, hH, hU, ?_, hM⟩
  have hi := NfMid.isNormal0_inv h0
  rw [inv_one] at hi
  have hback : g₀⁻¹ *ᵥ (g₀ *ᵥ w) = w := NfMid.inv_mul_vec hN.1 w
  have hi' : IsNormal0 k r le_rfl β 1 (g₀⁻¹ *ᵥ (g₀ *ᵥ w)) (g₀ *ᵥ w) g₀⁻¹ := by
    rw [hback]
    exact hi
  exact (isNormal0_iff (g₀ *ᵥ w)).1 hi'

end GlobalTheory.Amp.StabNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDensityOnEqFibreIntegral
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreDensity

theorem not_pos_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : ¬ 0 < h b := by
  intro hpos
  have hev : ∀ᶠ x in nhds b, h b / 2 < h x := by
    have h1 : ∀ᶠ x in nhdsWithin b B, h b / 2 < h x :=
      (hh b hb).eventually (lt_mem_nhds (by linarith))
    rwa [hB.nhdsWithin_eq hb] at h1
  obtain ⟨U, hUsub, hUo, hbU⟩ := mem_nhds_iff.1 (Filter.inter_mem (hB.mem_nhds hb) hev)
  obtain ⟨K, hK, hbK, hKU⟩ := exists_compact_subset hUo hbU
  have hKB : K ⊆ B := fun x hx => (hUsub (hKU hx)).1
  have hKh : ∀ x ∈ K, h b / 2 < h x := fun x hx => (hUsub (hKU hx)).2
  have hle : ∫ _ in K, h b / 2 ∂ν ≤ ∫ x in K, h x ∂ν :=
    setIntegral_mono_on (continuousOn_const.integrableOn_compact hK)
      ((hh.mono hKB).integrableOn_compact hK) hK.measurableSet (fun x hx => (hKh x hx).le)
  rw [setIntegral_const, h0 K hK hKB, smul_eq_mul] at hle
  have hKpos : 0 < ν K :=
    lt_of_lt_of_le (isOpen_interior.measure_pos ν ⟨b, hbK⟩) (measure_mono interior_subset)
  have hreal : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hK.measure_lt_top.ne
  have := mul_pos hreal (half_pos hpos)
  linarith

theorem eq_zero_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : h b = 0 := by
  have h1 := not_pos_of_setIntegral_isCompact_eq_zero ν hB hh h0 hb
  have h2 : ¬ 0 < -h b := not_pos_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => -h x) hh.neg
    (fun S hS hSB => by rw [integral_neg, h0 S hS hSB, neg_zero]) hb
  linarith [not_lt.1 h1, not_lt.1 h2]

theorem eq_of_setIntegral_isCompact_eq {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {g h : X → ℂ}
    (hg : ContinuousOn g B) (hh : ContinuousOn h B)
    (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, g x ∂ν = ∫ x in S, h x ∂ν)
    {b : X} (hb : b ∈ B) : g b = h b := by
  have hk : ContinuousOn (fun x => g x - h x) B := hg.sub hh
  have hint : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, (g x - h x) ∂ν = 0 := by
    intro S hS hSB
    rw [integral_sub ((hg.mono hSB).integrableOn_compact hS) ((hh.mono hSB).integrableOn_compact hS),
      h0 S hS hSB, sub_self]
  have hre : (g b - h b).re = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).re)
      (Complex.continuous_re.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.reCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.reCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_re]) hb
  have him : (g b - h b).im = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).im)
      (Complex.continuous_im.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.imCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.imCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_im]) hb
  have hz : g b - h b = 0 := Complex.ext (by simpa using hre) (by simpa using him)
  exact sub_eq_zero.1 hz

theorem contDensityOn_eq_fibre_integral : ∀ (V X : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (f : V → X) (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (fib : X → Measure V) (φ : V → ℝ) (g : X → ℂ), Continuous f → IsOpen B → IsFibreFamily μ f id Set.univ ν B fib → Continuous φ → HasCompactSupport φ → (∀ v, 0 ≤ φ v) → IsContDensityOn μ f id ν B (fun v => (φ v : ℂ)) g → ∀ b ∈ B, g b = ((∫ v, φ v ∂(fib b) : ℝ) : ℂ) ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (g b).re := by
  intro V X _ _ _ _ _ _ _ _ μ f ν _ _ B fib φ g hf hB hfib hφ hφc hφ0 hdens
  obtain ⟨hconc, hdis, hreg⟩ := hfib
  obtain ⟨hgc, hgint⟩ := hdens
  have hφm : Measurable φ := hφ.measurable
  obtain ⟨hφi, hGc⟩ := hreg φ hφ hφc (Set.subset_univ _)
  set G : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hG
  have hG0 : ∀ b, 0 ≤ G b := fun b => integral_nonneg (fun v => hφ0 v)
  have hlin : ∀ b ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (G b) := fun b hb =>
    (ofReal_integral_eq_lintegral_ofReal (hφi b hb) (Filter.Eventually.of_forall hφ0)).symm
  have key : ∀ S : Set X, IsCompact S → S ⊆ B →
      ∫ x in S, g x ∂ν = ∫ x in S, ((G x : ℝ) : ℂ) ∂ν := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    have hpre : MeasurableSet (f ⁻¹' S) := hf.measurable hSm

    have hL : ∫⁻ v in f ⁻¹' S, ENNReal.ofReal (φ v) ∂μ = ∫⁻ b in S, ENNReal.ofReal (G b) ∂ν := by
      have h2 := hdis ((f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)))
        ((ENNReal.measurable_ofReal.comp hφm).indicator hpre)
      rw [Measure.restrict_univ, lintegral_indicator hpre] at h2
      rw [h2, ← lintegral_indicator hSm]
      apply lintegral_congr
      intro b
      have hae : ∀ᵐ v ∂(fib b), f v = b := by
        rw [ae_iff]
        refine measure_mono_null ?_ (hconc b)
        intro v hv
        simpa using hv
      by_cases hbS : b ∈ S
      · rw [Set.indicator_of_mem hbS, ← hlin b (hSB hbS)]
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        simp [hv, hbS]
      · calc ∫⁻ v, (f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)) v ∂(fib b)
            = ∫⁻ _, 0 ∂(fib b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with v hv
              simp [hv, hbS]
          _ = S.indicator (fun b => ENNReal.ofReal (G b)) b := by
              simp [hbS]
    have hGS : IntegrableOn G S ν := (hGc.mono hSB).integrableOn_compact hS
    have hφS : ∫ v in f ⁻¹' S, φ v ∂μ = ∫ b in S, G b ∂ν := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
          hφ.aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
          hGS.integrable.aestronglyMeasurable, hL]
    have e := hgint S hS hSB
    simp only [Set.image_id] at e
    rw [← e, integral_complex_ofReal, integral_complex_ofReal, hφS]
  intro b hb
  have hgb : g b = ((G b : ℝ) : ℂ) :=
    eq_of_setIntegral_isCompact_eq ν hB hgc (Complex.continuous_ofReal.comp_continuousOn hGc) key hb
  refine ⟨hgb, ?_⟩
  rw [hlin b hb, hgb, Complex.ofReal_re]

end GlobalTheory.FibreDensity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMap
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MatMulDet

theorem det_real_mul_mul (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ))
    (hL : ∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family ..)

end GlobalTheory.MatMulDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAut
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm


open MeasureTheory NumberField Matrix Finset in
open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL : ∀ (E : Type) [Field E] [NumberField E],
    IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ →
      ∀ γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ, _root_.GlobalTheory.FlagMeas.detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  obtain ⟨κ, hκ, hcov⟩ := (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have hpos := _root_.GlobalTheory.OrbitTerm.detNorm_pos_of_mem_autGL hγ
  have h1 := (hcov γ hpos).2.1
  have h2 := (hcov (_root_.GlobalTheory.OrbitTerm.oneInf E j) (by
    rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf]; exact one_pos)).2.1
  rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf, div_one] at h2
  have hmul := _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul E j Λ hγ (_root_.GlobalTheory.OrbitTerm.oneInf E j)
  rw [_root_.GlobalTheory.OrbitTerm.mul_oneInf] at hmul
  rw [hmul, h2] at h1
  field_simp at h1
  linarith

end GlobalTheory.OrbitTerm
end

