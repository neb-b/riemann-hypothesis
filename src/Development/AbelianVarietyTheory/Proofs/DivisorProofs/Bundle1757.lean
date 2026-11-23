module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

namespace GlobalTheory.RunSizes


set_option maxHeartbeats 2000000 in
theorem core (f r k m PP TO T : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hm : 0 < m) (hkm : m ≤ k)
    (hPP : f * r ^ 2 ≤ PP) (hTO : PP ^ 4 * (f * (r * (r - 1) / 2)) ^ 3 * k / m ≤ TO) (hT0 : 0 ≤ T)
    (hT : T ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m + 1) :
    (f * (r * (r - 1) / 2) + 3) * ((f * (r * (r - 1) / 2) + 1) * (f * (r * (r - 1) / 2)) / 2 + 4 * r +
        f * (r * (r - 1) / 2) + 3) * (T + f * (r * (r - 1) / 2) + 1) + 4 ≤ TO ∧
      22 * f ^ 2 * r ^ 4 + 2 * r + 1 ≤ TO ∧
      f * (r * (r - 1) / 2) + 1 ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m := by
  set d := f * (r * (r - 1) / 2) with hd
  have hr1 : 5 ≤ r - 1 := by linarith
  have hrr : 5 * r ≤ r * (r - 1) := by nlinarith
  have hd5 : 5 * r ≤ d := by rw [hd]; nlinarith
  have hd30 : 30 ≤ d := by linarith
  have hdr2 : d ≤ f * r ^ 2 / 2 := by rw [hd]; nlinarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hkm' : 1 ≤ k / m := (one_le_div hm).2 hkm
  set A := PP ^ 2 * d ^ 2 * k / m with hA
  have hA' : A = PP ^ 2 * d ^ 2 * (k / m) := by rw [hA]; ring
  have hPP2 : 1 ≤ PP ^ 2 := by nlinarith
  have hAd : d ^ 2 ≤ A := by
    rw [hA']
    have h0 : 0 ≤ d ^ 2 := by positivity
    have : d ^ 2 ≤ PP ^ 2 * d ^ 2 := by nlinarith
    calc d ^ 2 ≤ PP ^ 2 * d ^ 2 := this
      _ = PP ^ 2 * d ^ 2 * 1 := by ring
      _ ≤ PP ^ 2 * d ^ 2 * (k / m) := by gcongr
  have hTO' : PP ^ 2 * d * A ≤ TO := by
    have : PP ^ 4 * d ^ 3 * k / m = PP ^ 2 * d * A := by rw [hA]; ring
    linarith
  have hG : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) ≤ d ^ 3 := by nlinarith
  have hT2 : T + d + 1 ≤ 2 * A := by nlinarith
  have hGnn : 0 ≤ (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) := by
    have : 0 ≤ r := by linarith
    positivity
  have h3d : 3 * d ^ 2 ≤ PP ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by nlinarith
  have hd1 : d + 1 ≤ d ^ 2 := by nlinarith
  refine ⟨?_, ?_, by linarith⟩
  · have h1 : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) * (T + d + 1) ≤ d ^ 3 * (2 * A) :=
      mul_le_mul hG hT2 (by linarith) (by positivity)
    have h4 : 4 ≤ d ^ 3 * A := by nlinarith
    have h2 : d ^ 3 * (2 * A) + 4 ≤ PP ^ 2 * d * A := by
      have : 3 * d ^ 2 * (d * A) ≤ PP ^ 2 * (d * A) := by
        apply mul_le_mul_of_nonneg_right h3d; positivity
      nlinarith
    linarith
  · have hP2 : (f * r ^ 2) ^ 2 ≤ PP ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hPP
    have hd900 : (30 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) hd30 2
    have hA1 : 1 ≤ A := by linarith
    have hdA : 30 ≤ d * A := by
      calc (30 : ℝ) = 30 * 1 := by ring
        _ ≤ d * A := mul_le_mul hd30 hA1 (by norm_num) (by linarith)
    have hr4 : r * 216 ≤ r ^ 4 := by
      have h3 : (6 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
      have : r ^ 4 = r * r ^ 3 := by ring
      rw [this]
      have h216 : (216 : ℝ) ≤ r ^ 3 := by norm_num at h3; linarith
      have hr0 : (0 : ℝ) ≤ r := by linarith
      exact mul_le_mul_of_nonneg_left h216 hr0
    have hf2 : (2 : ℝ) ^ 2 ≤ f ^ 2 := pow_le_pow_left₀ (by norm_num) hf 2
    norm_num at hf2
    have hfr : 2 * r + 1 ≤ f ^ 2 * r ^ 4 := by
      have : 4 * (r * 216) ≤ f ^ 2 * r ^ 4 := mul_le_mul hf2 hr4 (by positivity) (by positivity)
      linarith
    have h30 : (f * r ^ 2) ^ 2 * 30 ≤ PP ^ 2 * (d * A) := by
      apply mul_le_mul hP2 hdA (by norm_num) (by positivity)
    have e1 : (f * r ^ 2) ^ 2 = f ^ 2 * r ^ 4 := by ring
    have e2 : PP ^ 2 * (d * A) = PP ^ 2 * d * A := by ring
    rw [e1, e2] at h30
    linarith


set_option maxHeartbeats 2000000 in
theorem at_point {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Tp : ParamsT D L P) :
    1 ≤ D.R.f * D.R.r.choose 2 ∧
    D.R.f * D.R.r.choose 2 + 1 ≤
      ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = (D.R.f * D.R.r.choose 2 + 3) *
        ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r + D.R.f * D.R.r.choose 2 + 3) →
      T = ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ →
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤ min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) ∧
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 +
        2 * D.R.r + 1 ≤ LevelStarExponents.h0 L := by
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hrR : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < D.R.m := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    linarith
  have hkmR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hDd : ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    push_cast [Nat.cast_choose_two]; ring
  have hdpos : (0 : ℝ) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [← hDd]; positivity

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hZ : 1 ≤ zBase L := by
    unfold zBase
    have : (12 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hPP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Tp.PP := by
    rw [Tp.PP_eq]
    have h1 : zBase L ^ (2 : ℝ) ≤ zBase L ^ Tp.eP :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Tp.eP_ge])
    rw [Real.rpow_two] at h1
    have hL2 : 1 ≤ L.sc.L ^ 2 := one_le_pow₀ hL
    have hff : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 * L.sc.L ^ 2 := by nlinarith
    have h3 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2 := by
      unfold zBase
      calc (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ ((D.R.f : ℝ) ^ 2 * L.sc.L ^ 2) * (D.R.r : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hff (sq_nonneg _)
        _ = ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 := by ring
    have hCP := Tp.one_le_CP
    have h4 : 0 ≤ zBase L ^ Tp.eP := Real.rpow_nonneg (by linarith) _
    nlinarith

  have hTO : Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k / D.R.m ≤ (Tp.TO : ℝ) := by
    have hTOg := Tp.TO_ge
    rw [Tp.Dp_eq, hDd] at hTOg
    refine le_trans ?_ hTOg
    have hxc : 1 ≤ L.sc.x ^ Tp.Cp := Real.one_le_rpow hx1 Tp.Cp_nonneg
    have hde := L.thickDensity_pos
    have hde1 := L.thickDensity_le_one
    rw [div_le_div_iff₀ hmR (mul_pos hmR hde)]
    have hB : 0 ≤ Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k := by
      have : (0 : ℝ) ≤ D.R.k := by positivity
      positivity
    have hfx : L.de2 ≤ (D.R.f : ℝ) * L.sc.x ^ Tp.Cp := by nlinarith
    have := mul_le_mul_of_nonneg_left hfx (mul_nonneg hB hmR.le)
    nlinarith
  have hPPnn : 0 ≤ Tp.PP := le_trans (by positivity) hPP
  have hA0 : 0 ≤ Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by positivity
  have hT0 := Nat.ceil_lt_add_one hA0
  rw [hDd] at hT0 hA0
  obtain ⟨c1, c2, c3⟩ := core (D.R.f : ℝ) (D.R.r : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) Tp.PP (Tp.TO : ℝ)
    (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ)
    hfR hrR hmR hkmR hPP hTO (Nat.cast_nonneg _) hT0.le

  have hTOt : Tp.TO ≤ D.R.t := by
    have hs := Tp.split
    have h40 := Tp.nW_40
    have hn0 := Tp.order_ge_rank_bound
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ h40
    have : D.R.r ≤ Tp.TO := le_trans (Nat.le_add_right _ _) hn0
    omega
  have hTON : Tp.TO ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : D.R.t ≤ D.R.m * (D.R.t + 1) := by nlinarith
    omega
  have hgap : (Tp.TO : ℝ) ≤ LevelStarExponents.gapS D P.Cgap := by
    unfold LevelStarExponents.gapS
    have h1 : ((Tp.TO : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hTON
    have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D.R.m by omega))
    have h3 : 0 ≤ P.Cgap * D.R.k * (D.R.m : ℝ) ^ 4 := by
      have := P.Cgap_pos
      positivity
    have h4 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by
      have : (0 : ℝ) ≤ D.R.N D.R.m := by positivity
      nlinarith
    linarith
  have hTO1 : (1 : ℝ) ≤ Tp.TO := by
    have := Tp.TO_40
    have : 1 ≤ Tp.TO := by omega
    exact_mod_cast this
  have hh0 : 2 * (Tp.TO : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := by positivity
    nlinarith
  refine ⟨Nat.mul_pos (by omega) (Nat.choose_pos (by omega)), ?_, ?_⟩
  · have h : ((D.R.f * D.R.r.choose 2 + 1 : ℕ) : ℝ) ≤
        Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one, hDd]; exact c3
    exact_mod_cast h.trans (Nat.le_ceil _)
  · intro G T hG hT
    subst hG hT
    rw [hDd]
    have e : ((((D.R.f * D.R.r.choose 2 + 3) * ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r +
          D.R.f * D.R.r.choose 2 + 3)) *
        (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ +
          D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) =
        ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          (((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) / 2 +
            4 * (D.R.r : ℝ) + (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          ((⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) +
            (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) := by
      push_cast [Nat.cast_choose_two]; ring
    rw [e]
    refine ⟨le_min (by linarith) (by linarith), by linarith⟩

theorem gaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι => at_point (Fm.parT x hx ι)⟩⟩⟩

end GlobalTheory.RunSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApply
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblGenV

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem KD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD (g * h) - 1 = matD g * (matD h - 1) + (matD g - 1) := by
      rw [matD_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    show u • (matD (g * h) - 1) = 0
    have h1 : u • (matD h - 1) = 0 := hh.1 u hu
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
    · rw [_root_.mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem KD_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    show u • (matD g⁻¹ - 1) = 0
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem PDiag_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {p : UD σ W} (hp : p ∈ PDiag σ W) :
    p⁻¹ ∈ PDiag σ W := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t⁻¹, ?_⟩
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hDdef
  set T : Matrix (Fin d) (Fin d) (AE F E) := (t : Matrix (Fin d) (Fin d) (AE F E)) with hT
  set Ti : Matrix (Fin d) (Fin d) (AE F E) := ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) with hTi
  have hTT : T * Ti = 1 := by rw [hT, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ht' : matD p * D = D * T := ht
  have key : matD p⁻¹ * (D * T) = D := by
    rw [← ht', ← Matrix.mul_assoc, matD_inv_mul, Matrix.one_mul]
  show matD p⁻¹ * D = D * Ti
  calc matD p⁻¹ * D = matD p⁻¹ * (D * T) * Ti := by
        rw [Matrix.mul_assoc (matD p⁻¹), Matrix.mul_assoc D, hTT, Matrix.mul_one]
    _ = D * Ti := by rw [key]

end GlobalTheory.DblGenV

namespace GlobalTheory.DblGenV

theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B a (a - G.p) G.p G.V hT.base hT.geo.hV v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ a G.V v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

end GlobalTheory.DblGenV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortValueAtPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.ShortPtVal


set_option maxHeartbeats 2000000 in
theorem short_value_at_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (χ : (AE D)ˣ →* Circle) (c0' : ℂ), (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → ∀ (ζ : ℂ) (φc : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ), ζ ≠ 0 → GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc = (fun q => ζ * (O i).s0 ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q))) → ∀ (F₀ : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P F₀ → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk → GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → GlobalTheory.SW.SelfD X X.Λ → ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ D.R.r), x ∈ X.dom → x = GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1) → ∀ (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.Dict.IsMark T.Q.l X.Λ mk → GlobalTheory.AdTh.MarkAd T.Q.l (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → ∀ (v : GlobalTheory.SW.TF (Vc D i).rank g') (ϑ : (Fin g' → ℂ) → ℂ) (κ' : ℂ), GlobalTheory.SW.IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E (Vc D i).rank) X.Λ) v → (∀ z : Fin (Vc D i).rank → Fin g' → ℂ, ∏ b, ϑ (z b) = κ' * GlobalTheory.SW.thA X Dc.bas Dc.idx v x z) → letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra; ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) T.Q.c ℂ) (B : GlobalTheory.Dict.AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ → ∃ (mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E), GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ ∧ GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk₂ ∧ GlobalTheory.Dict.IsRoots (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ N Y ∧ evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c F₀ y = c0' * ((χ xk : Circle) : ℂ) * ((((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) * κ' * ζ⁻¹ * GlobalTheory.SW.thP X Dc.hr Dc.bas Dc.idx (GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc) Y) (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins χ c0' hcov Λ N x₀ P hUn hTb hTl hLev hAdm hP ζ φc hζ hhat F₀ hF₀
    X g' Dc k xk hk hX hp hΛ hsd x hx hxk mk hm hma v ϑ κ' hv hκ
  intro y B hB hϑ
  subst hxk
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ :=
    ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm :
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra
  have hj := inR i
  have halg : ∀ t : T.Q.c.F, algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF t) = algebraMap T.Q.c.F ℂ t := fun t => rfl
  have hTie : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTie i (O i).s0 hs
  obtain ⟨-, -, -, -, hrk, hpq, -, -, -, -, hD, -⟩ := hmod ((O i).dict k).1
  obtain ⟨hemb, -, -, -⟩ := GlobalTheory.PtId.dict_cast T.J hT.j _ hj (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  have hlev := hT.sh.dLev _ hj (Vc D i).rank
  have hA₂ := hT.lvA _ hj (Vc D i).rank
  have hA : T.Q.l.A = 1 := hT.j.pins.2.1.2
  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D _ _ T.Q.l (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) _
    (rank_Wc i) (iotaW T.J i) hemb (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) k
  rw [hΛ] at hm₂ hov
  have hM : 0 < (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M := lt_of_lt_of_le (by norm_num) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hLev.1.pos
  refine ⟨mk₂, Y, hm₂, ha₂, hY, ?_⟩
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := GlobalTheory.Dict.MarkLift.exists_lift_marked _ _ _ _ _ T.Q.c _
    (T.dδ ((i : ℕ) + 1) (Vc D i).rank) halg hlev hA hA₂ (fun e0 => absurd e0 hpq) _ g' X Dc.bas Dc.idx Dc.e _ X.Λ y B
    Dc.sympl hx hsd mk mk₂ hm hB hm₂ (hov mk hm.mem hma)
  obtain ⟨vv, hvv, hev⟩ := hF₀ ℂ halg y y₂ hov₂
  obtain ⟨_, hnab'⟩ := hT.sh.dNab _ hj (Vc D i).rank
  have hVset : Λ.La ∈ GlobalTheory.SW.Vset D.host.E (Vc D i).rank (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ Λ.La).2.1 _ N hM hUn hTl hLev
  have hP2 := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank)).2 (wtA (κ i)) _ hP.1
  have e1 := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ _ D.R.r g' X Dc.bas Dc.idx Dc.e _ X.Λ y₂ B₂
    Dc.sympl hx hsd _ (Vc D i).rank Dc.hr Dc.eL hrk hD.2 Dc.dir_eq _ hnab' ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂
    Λ.La hVset N hLev Y hY (wtA (κ i)) _ hP2 _ _ vv hvv
  have hc := hcov X g' Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂
  rw [hev, e1, hc]
  have hW : (fun q => algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q)) =
      ζ⁻¹ • GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc := by
    funext q
    rw [hhat, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hζ]
    rfl
  have hpoly : MvPolynomial.map (algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ)
      (MvPolynomial.map ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF : T.Q.c.F →+* (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F) P) =
      MvPolynomial.map (O i).s0 P := by
    rw [MvPolynomial.map_map]
    congr 1
  have hg : ∀ (W : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ) (a : ℂ),
      GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (a • W) Y =
        a • GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v W Y := fun W a => by
    simp only [GlobalTheory.Dict.gphi, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [smul_finsum]
  have hs0 : ∀ t : T.Q.c.F, algebraMap T.Q.c.F ℂ t = (O i).s0 t := fun t => rfl
  rw [hW, hpoly, hg, GlobalTheory.Dict.ShortPt.theta_smul₂]
  simp only [map_mul, map_inv₀, map_natCast, halg, hs0]
  ring

end GlobalTheory.ShortPtVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartNonzeroIndexPlacesTwisted
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
open GlobalTheory.CharRealise
open Formalism.DivisionValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)


set_option maxHeartbeats 4000000 in
theorem splitPartFace_baseLevel_indices_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw i p.P.A3.A.μ0 w = ((p.R.toRealDat.toCx (F2 p)).data (F2 p).cr false).Iw i p.P.A3.A.μ0 w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw i _ w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl


set_option maxHeartbeats 4000000 in
theorem splitPartFace_baseLevel_jw_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    jw ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).HT i p.P.A3.A.μ0) w ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).Tl i p.P.A3.A.μ0) =
      jw ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).HT i p.P.A3.A.μ0) w
        ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).Tl i p.P.A3.A.μ0) := by
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl


set_option maxHeartbeats 4000000 in
theorem w1_of_inW1_split_part (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (h : p.R.toRealDat.NonzeroIndexPlace (F2 p) w) :
    (p.R.toCx3 p.F).W1 p.F.cr (p.N C CH) w := by
  obtain ⟨w', hw', i, h⟩ := h
  refine ⟨i, ?_⟩
  rcases hw' with rfl | rfl
  · rcases h with h | h | h | h | h
    · exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · exact Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem tupTw_of_w1Row : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p h w hw
  exact h w (w1_of_inW1_split_part p 0 0 w hw)

end GlobalTheory.BigOn

end
end

