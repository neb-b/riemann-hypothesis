module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasDim

theorem two_mul_card_pairs_le (p : ℕ) :
    2 * ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p ^ 2 := by
  have e : ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card = ∑ i ∈ Finset.range p, i := by
    rw [← Finset.sum_range_reflect]
    rw [Fin.sum_univ_eq_sum_range (fun i => p - 1 - i) p |>.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [e, mul_comm, Finset.sum_range_id_mul_two]
  rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem abs_factor_le (d : ℤ) (i j : ℕ) (hij : i < j) :
    |((((d : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) : ℚ) : ℝ)| ≤ 1 + |(d : ℝ)| := by
  have hs : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hs0 : (0 : ℝ) < (j : ℝ) - (i : ℝ) := by linarith
  push_cast
  rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have h1 : |(d : ℝ) + (j : ℝ) - (i : ℝ)| ≤ |(d : ℝ)| + ((j : ℝ) - (i : ℝ)) := by
    have := abs_add_le (d : ℝ) ((j : ℝ) - (i : ℝ))
    rw [abs_of_pos hs0] at this
    rw [show (d : ℝ) + (j : ℝ) - (i : ℝ) = (d : ℝ) + ((j : ℝ) - (i : ℝ)) by ring]
    exact this
  nlinarith [abs_nonneg (d : ℝ)]

theorem abs_weylDimU_le {p : ℕ} (lam : Fin p → ℤ) (B : ℝ) (hB : ∀ a b, |((lam a - lam b : ℤ) : ℝ)| ≤ B) :
    |((Formalism.IndefR.Mult.weylDimU lam : ℚ) : ℝ)| ≤
      (1 + B) ^ (∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card) := by
  unfold Formalism.IndefR.Mult.weylDimU
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.1 hj).2
  have := abs_factor_le (lam i - lam j) i j hij
  exact this.trans (by linarith [hB i j])

end GlobalTheory.OneMeasDim

namespace GlobalTheory.OneMeasDim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem abs_wt_sub_le (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a b : Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) :
    |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
  have hw : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hab : a = b
  · subst hab; simpa using hw
  set c : ℝ := (((D.hc τ).e i : ℚ) : ℝ)
  set g : (Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) → ℝ :=
    fun x => |((Formalism.L2.NTheta.wtOf D (Wc D i) τ x : ℤ) : ℝ) + c| with hg
  have h1 : |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ g a + g b := by
    rw [hg]; push_cast
    have := abs_sub (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c)
    rw [show (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) - (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c) =
      ((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) - ((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) by ring] at this
    exact this
  have h2 : g a + g b ≤ ∑ x, g x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 : ∑ x, g x ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
    exact Finset.single_le_sum (f := fun τ' => ∑ x, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ' x : ℤ) : ℝ) + (((D.hc τ').e i : ℚ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  linarith

theorem log_dimAt_le : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau),
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  intro D i L hL τ
  obtain ⟨hf, hs, -, -⟩ := hL

  have hb2 : (2 : ℝ) ≤ Real.exp L := by
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
    have hfn : 2 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
    have hn : 1 ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    have : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by
      have : 2 ≤ D.R.f * D.R.r * D.R.nV := by
        calc 2 ≤ D.R.f := hfn
          _ = D.R.f * 1 * 1 := by ring
          _ ≤ D.R.f * D.R.r * D.R.nV := by gcongr
      exact_mod_cast this
    linarith
  have hL0 : 0 ≤ L := by
    by_contra h; push_neg at h
    have := Real.exp_lt_exp.2 h; rw [Real.exp_zero] at this; linarith
  set b := Real.exp L with hbdef
  set B := b ^ 2
  have h1B : 1 + B ≤ Real.exp (3 * L) := by
    rw [show 3 * L = L + L + L by ring, Real.exp_add, Real.exp_add, ← hbdef]
    nlinarith
  have hlog1B : Real.log (1 + B) ≤ 3 * L := by
    have := Real.log_le_log (by positivity) h1B
    rwa [Real.log_exp] at this

  set p := ((Wc D i).sig (tauE D τ)).1
  set q := ((Wc D i).sig (tauE D τ)).2
  have hpq : p + q = D.R.r := by
    have hr := D.sp.W_rank ((i:ℕ)+1) (by omega) (by have := i.2; omega)
    rw [← hr]; obtain ⟨e, -⟩ := (D.sp.W_sig ((i:ℕ)+1)) (tauE D τ); simpa using (Fintype.card_congr e).symm
  set κ := Formalism.L2.NTheta.wtOf D (Wc D i) τ
  have hent : ∀ a b, |((κ a - κ b : ℤ) : ℝ)| ≤ B := fun a b => (abs_wt_sub_le D i τ a b).trans (hs i)
  set N1 := ∑ a : Fin p, (Finset.univ.filter (fun j : Fin p => a < j)).card
  set N2 := ∑ a : Fin q, (Finset.univ.filter (fun j : Fin q => a < j)).card
  have w1 := abs_weylDimU_le (fun a => κ (Sum.inl a)) B (fun a b => hent _ _)
  have w2 := abs_weylDimU_le (fun a => κ (Sum.inr a)) B (fun a b => hent _ _)
  have hdim : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ =
      ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inl a)) : ℚ) : ℝ) *
        ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inr a)) : ℚ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK; push_cast; rfl
  have habs : |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| ≤ (1 + B) ^ (N1 + N2) := by
    rw [hdim, abs_mul, pow_add]
    exact mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
  have hlog : Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := by
    rw [← Real.log_abs]
    rcases eq_or_ne (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) 0 with h0 | h0
    · rw [h0, abs_zero, Real.log_zero]
      have hB0 : (0 : ℝ) ≤ B := sq_nonneg b
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    · have := Real.log_le_log (abs_pos.2 h0) habs
      rwa [Real.log_pow] at this
  have hN : 2 * (N1 + N2) ≤ D.R.r ^ 2 := by
    have a1 : 2 * N1 ≤ p ^ 2 := two_mul_card_pairs_le p
    have a2 : 2 * N2 ≤ q ^ 2 := two_mul_card_pairs_le q
    have a3 : p ^ 2 + q ^ 2 ≤ (p + q) ^ 2 := by ring_nf; omega
    rw [← hpq]; omega
  have hN' : 2 * ((N1 + N2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ ((N1 + N2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := hlog
    _ ≤ ((N1 + N2 : ℕ) : ℝ) * (3 * L) := mul_le_mul_of_nonneg_left hlog1B hN0
    _ = 3 / 2 * (2 * ((N1 + N2 : ℕ) : ℝ)) * L := by ring
    _ ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by gcongr

end GlobalTheory.OneMeasDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.DilKer

open GlobalTheory.StdFrames (cpt)

theorem frMapO_dil {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    (a : D.host.E) (z : WO (Vc D i) (Wc D i)) :
    frMapO (Vc D i) (Wc D i) βS βT (dil i a z) = eToEAf D a • frMapO (Vc D i) (Wc D i) βS βT z := by
  have h : (dil i a z).map (toEAf D) = eToEAf D a • z.map (toEAf D) := by
    ext k l
    simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, GlobalTheory.IdemIntegral.toEAf_incA]
  simp only [frMapO, h, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_dil {D : D7} (i : Fin D.R.m) (e : AE D) (a : D.host.E) {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) :
    IsHalf e (dil i a z) := fun k l => by
  simp only [dil, Matrix.map_apply]
  rw [mul_left_comm, hz k l]

theorem frMapO_half {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    {e : AE D} {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) (k l) :
    toEAf D e * frMapO (Vc D i) (Wc D i) βS βT z k l = frMapO (Vc D i) (Wc D i) βS βT z k l := by
  have h : z.map (toEAf D) = toEAf D e • z.map (toEAf D) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← RingHom.map_mul, hz a b]
  have h2 : frMapO (Vc D i) (Wc D i) βS βT z = toEAf D e • frMapO (Vc D i) (Wc D i) βS βT z := by
    conv_lhs => rw [frMapO, h]
    simp only [frMapO, Matrix.mul_smul, Matrix.smul_mul]
  conv_rhs => rw [h2]
  rfl

theorem val_cpt_eToEAf {D : D7} (PP : Pl D.host.E) (x : D.host.E) :
    Valued.v (cpt PP (eToEAf D x)) = PP.valuation D.host.E x := by
  have : eToEAf D x = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D x := rfl
  rw [this, GlobalTheory.AdIsom.cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]

theorem mem_int_of_mul {D : D7} {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {m : EAf D} (hm : toEAf D e * m = m)
    (hy : eToEAf D (ϖ : D.host.E) * m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hr : ∀ PP ∈ Q, Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * m)) < 1) :
    m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine (GlobalTheory.AdIsom.mem_OA m).2 fun P => ?_
  by_cases hP : P ∈ Q
  · have h1 := hr P hP
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ P hP).1 (hϖ P hP).2] at h1
    by_cases h0 : Valued.v (cpt P m) = 0
    · rw [h0]; exact zero_le'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (cpt P m) = WithZero.exp k := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hk] at h1 ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have h0 : cpt P (toEAf D (∑ PP ∈ Q, es PP)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 P fun h => hP (h ▸ hPP)
    have := congrArg (cpt P) hm
    rw [RingHom.map_mul, h0, zero_mul] at this
    rw [← this, Valuation.map_zero]
    exact zero_le'

theorem mem_localLattice_iff_redM : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : WO (Vc D i) (Wc D i), IsHalf eQ z → dil i (ϖ : D.host.E) z ∈ lattice₂ R i → (z ∈ lattice₂ R i ↔ ∀ PP ∈ Q, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) z)) = 0) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV Q hQ eQ he ϖ hϖ0 hϖ z hz hϖz
  have hI := _root_.GlobalTheory.HalfLatInt.isIntM_iff_mem_latP D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ he
  rw [frMapO_dil]
  constructor
  · intro hzL PP hPP
    have hM := (hI z hz).2 hzL
    ext k l
    have hϖi : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← GlobalTheory.IdemIntegral.toEAf_incA]
      exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (GlobalTheory.SplitIndex.finPart_incA_mem ϖ)
    have hint : eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hϖi (hM k l)
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos hint]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hint⟩).2 ?_
    change Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * _)) < 1
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ PP hPP).1 (hϖ PP hPP).2]
    calc WithZero.exp (-1 : ℤ) * Valued.v (cpt PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l))
        ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr; exact (GlobalTheory.AdIsom.mem_OA _).1 (hM k l) PP
      _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro hred
    have hN := (hI _ (isHalf_dil i eQ _ hz)).2 hϖz
    rw [frMapO_dil] at hN
    have hN' : ∀ k l, eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun k l => hN k l
    refine (hI z hz).1 fun k l => mem_int_of_mul he hϖ (frMapO_half i _ _ hz k l) (hN' k l) fun PP hPP => ?_
    have h1 := congrFun (congrFun (hred PP hPP) k) l
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos (hN' k l)] at h1
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hN' k l⟩).1 h1

end GlobalTheory.DilKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
section
noncomputable section

section Family

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg GlobalTheory.KeyFourth
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyCover


set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem nonempty_keySec_of_family (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (hpq : 1 ≤ Dw.p + Dw.q) (hF : FnAlgClosed (Xo := Xo) (c := c)) : Nonempty (KeySec Xo c) := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (_root_.GlobalTheory.FrameUnif.nonempty_thetaData E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => _root_.GlobalTheory.FrameUnif.exists_isNormUn hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => _root_.GlobalTheory.NormFrame.frameOK_of_isNormUn hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => _root_.GlobalTheory.NormUnBor.normUn_bor hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => _root_.GlobalTheory.FrameUnif.normUn_gamma hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => _root_.GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have hchart : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧
        GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
    have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
      charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    choose Ψ hΨ using fun Z : Comp Xo c => _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
    refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
    haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
    obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e C.R C.y hpq
    obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om C.Z) C.yg hpq
    obtain ⟨u, hu⟩ := k₄ C.R Φ.key
    refine ⟨Φ, u, hΦ, hu, ?_⟩
    rw [← _root_.GlobalTheory.KeyFourth.rule_frBor κ k₁ k₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
    exact (hu (Om C.Z) _ _ (_root_.GlobalTheory.KeyFourth.tied_keyPB E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
  obtain ⟨v, hv⟩ := hchart
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => _root_.GlobalTheory.KeyFourth.continuousOn_rootVal E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @_root_.GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@_root_.GlobalTheory.KeyFourth.tied_keyPB E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyCover

end Family

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.KeyCover

end GlobalTheory.KeyCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorFlatLineEqGramOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegOrtho

theorem homFac_eq_gram_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (t : Ix Dw → (CAt (σ.comp (algebraMap c.F K)))ˣ), ((U (σ.comp (algebraMap c.F K))).X k).IsOrtho w.1 → FrBor t ((U (σ.comp (algebraMap c.F K))).un k w) z → GlobalTheory.CompHS.homFac (U (σ.comp (algebraMap c.F K))) x (flatWt Dw τ) k w = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL τ K _ _ _ y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ hφ z hz k w t hort hbor
  have hU := hL.unf _ hσ
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k w
  obtain ⟨Wu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unitAt W (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hort)
  have hHm := GlobalTheory.OrthoHerm.hm_eq_smul_one E H Dw l Xo c _ r (U _) x hσ hU k w W Wu (hL.xi _ hσ k) hort
  obtain ⟨hzx, hcomb, -⟩ := hbor
  choose C hCi hCup hCc using hcomb
  have hp : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

  have hx : 0 < x := by
    have hne : Nonempty (Σ ρ : E →+* ℂ, Fin (Dw.mult ρ)) := by
      rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
      · have hq1 : 0 < Dw.q := by have := hL.pos; omega
        exact ⟨⟨conjEmb τ.1, ⟨0, hq ▸ hq1⟩⟩⟩
      · exact ⟨⟨τ.1, ⟨0, hp ▸ h0⟩⟩⟩
    obtain ⟨j0⟩ := hne
    have h1 := Wu.pos (Pi.single (W.e.symm j0) 1) (by simp)
    rw [hHm] at h1
    have h2 : hermForm (((2 * x : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) (Pi.single (W.e.symm j0) 1)
        (Pi.single (W.e.symm j0) 1) = ((2 * x : ℝ) : ℂ) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct, Pi.single_apply]
    rw [h2, Complex.ofReal_re] at h1
    linarith
  have key : ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v →
      (h.gram σ v).det.re = (2 * Real.pi * x) ^ (Dw.mult ρ) *
        (∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖) ^ 2 := by
    intro ρ v hv
    rw [_root_.GlobalTheory.LieGram.gram_det_re_eq E H Dw l Xo c r U x hL K y B t₀ m1 m2 F h hh ρ v hv σ hσ φ hφ z hz k w W Wu hzx (C ρ) (hCc ρ), hHm,
      _root_.GlobalTheory.det_gram_lowerTriangular_coordVec_re W.g (Dw.mult ρ) (fun l => W.e.symm ⟨ρ, l⟩) (fun a b e => by simpa using e) (2 * x)
        (fun i j => toC (C ρ i j)) (fun i j hij => by simp only [hCup ρ i j hij]; rfl), ← Finset.prod_pow]
    simp only [hCi]
    congr 1
    ring
  rw [_root_.GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho E H Dw l Xo c _ r (U _) x τ k w hort, _root_.GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt E H Dw l c _ τ t, key _ u hu, key _ u' hu']
  have e1 : (2 * Real.pi * x) ^ (Dw.mult τ.1) = (2 * Real.pi * x) ^ Dw.p := by rw [hp]
  have e2 : (2 * Real.pi * x) ^ (Dw.mult (conjEmb τ.1)) = (2 * Real.pi * x) ^ Dw.q := by rw [hq]
  rw [e1, e2]
  have hpos : ∀ ρ : E →+* ℂ, 0 < ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ :=
    fun ρ => Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _)
  have hP := hpos τ.1
  have hP' := hpos (conjEmb τ.1)
  generalize ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P at *
  generalize ∏ i : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P' at *
  have ha : 0 < 2 * Real.pi * x := by positivity
  have hs : ∀ n : ℕ, Real.sqrt ((2 * Real.pi * x) ^ n) = Real.exp ((n : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_sq hP.le, Real.sqrt_sq hP'.le,
    hs, hs]
  have hq2 : Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) * Real.exp ((Dw.q : ℝ) / 2 * Real.log (2 * Real.pi * x)) =
      Real.exp ((Dw.p : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hq2]
  field_simp

end GlobalTheory.PtDegOrtho
end
end

