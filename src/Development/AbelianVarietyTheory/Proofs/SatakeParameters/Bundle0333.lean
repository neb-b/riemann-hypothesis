module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.ChartPosEqOfIw
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPow
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem lambdaCharacter_norm_eq_p_pow_of_pos : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hSpl hPos j hj hFill x hx
  have hsc : ∀ y, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  have hσ : ∀ a, sigD D (sigD D a) = a := fun a => by rw [hsc a]; exact Formalism.L2.PairingIndexBounds.F.sigD_conj D a
  obtain ⟨m, z, k, hm, hz, hkU, hkI, hxm⟩ := exists_pow_normOne_idele_eq_principal_mul_integralUnit _ _ (sigD D) hσ x hx
  have hz' : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by rw [← hsc]; exact hz
  have hzU := GlobalTheory.TwV.MuLawPf.rationalIdele_mem_normOne_of_norm_eq_one z hz'
  have hmul := S.law.mu_mul j hj
  have hpow : ∀ n : ℕ, S.muT (j + 1) (x ^ n) = S.muT (j + 1) x ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, hmul.1]
    | succ n ih => rw [pow_succ, pow_succ, hmul.2 _ (pow_mem hx n) _ hx, ih]
  have hsplit : S.muT (j + 1) x ^ m = S.muT (j + 1) (ratId D.host.F D.host.E z) * S.muT (j + 1) k := by
    rw [← hpow, hxm, hmul.2 _ hzU _ hkU]
  obtain ⟨e, he, hrat⟩ := S.law.mu_rat j hj

  obtain ⟨y, hy⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hkU
  obtain ⟨n, hn, hroot⟩ := GlobalTheory.TieFinOrd.mt_finite_order J.A J.dtU J.a J.pins J.tie j hj y (by rw [hy]; exact hkI)
  have hkroot : S.muT (j + 1) k ^ n = 1 := by
    rw [← hy, S.law.mu_read j hj y, ← Units.val_pow_eq_pow_val, hroot, Units.val_one]

  have ha := S.law.mu_alg j hj x hx
  have hb := S.law.mu_alg j hj _ hzU
  have hc := S.law.mu_alg j hj k hkU
  have hlamC : ∀ (a : ℂ) (h : a ∈ TaylorLogMetric.Qbar), TaylorLogMetric.lamC S.lam a = S.lam ⟨a, h⟩ := fun a h => by
    unfold TaylorLogMetric.lamC; rw [dite_eq_left h]
  have eQ : (⟨S.muT (j + 1) x, ha⟩ : TaylorLogMetric.Qbar) ^ m = ⟨_, hb⟩ * ⟨_, hc⟩ := Subtype.ext (by push_cast; exact hsplit)
  have eQk : (⟨S.muT (j + 1) k, hc⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by push_cast; exact hkroot)
  have hnormk : ‖S.lam ⟨_, hc⟩‖ = 1 := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQk
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hnorm_m : ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ ^ m = ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) (ratId D.host.F D.host.E z))‖ := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQ
    simp only [map_pow, norm_pow, map_mul, norm_mul, hnormk, mul_one] at h1
    rw [hlamC _ ha, hlamC _ hb]
    exact h1
  have hratN := GlobalTheory.TwU.RatNorm.norm_lamC_type_normOne D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos e (z : D.host.E) hz'
  rw [← hrat z hz'] at hratN

  have hvm : ∀ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) = ∑ s : Fin ((sysS H X std).G.P.n' v), (if IsOddPos s then -1 else 1) * e (hT.gat_pos u w hg ⟨v, s⟩) := by
    intro v
    refine vm_shift_cancels _ (sysS H X std) v (j + 1) (fun s => e (hT.gat_pos u w hg ⟨v, s⟩))
      (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)) (fun s => ?_)
    rw [hFill e he v s, sub_sub]

  have hord : ∀ v : (sysS H X std).Pl, (m : ℤ) * ordA (A0 J) v x = ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v (z : D.host.E)) := by
    intro v
    obtain ⟨hadd, hint, hratO, -⟩ := OrdA.ordA_props _ _ _ _ _ (A0 J) J.one.int hSpl.1 v
    have hp : ∀ n : ℕ, ordA (A0 J) v (x ^ n) = n * ordA (A0 J) v x := by
      intro n
      induction n with
      | zero =>
        have h1 := hadd 1 1
        rw [mul_one] at h1
        rw [pow_zero, Nat.cast_zero, zero_mul]
        linarith
      | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
    rw [← hp, hxm, hadd, hratO, hint k hkI, add_zero]
  rw [← pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) hm.ne', hnorm_m, hratN, ← zpow_natCast, ← zpow_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hvm v, ← hord v]
  ring

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.NormOne

variable {p : ℕ} [Fact p.Prime]

theorem norm_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ ≤ 1 := by
  rw [(X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_sigma_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
  rw [hy]
  exact norm_alg_le X E v _

theorem norm_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (u : (X.G.P.W v)ˣ) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ = 1 ∧
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ = 1 := by
  have h1 : ((u : X.G.P.W v) * ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := Units.mul_inv u
  have e1 : ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ *
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, norm_one]
  have e2 : ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ *
      ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, map_one, norm_one]
  have a1 := norm_alg_le X E v (u : X.G.P.W v)
  have a2 := norm_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have b1 := norm_sigma_alg_le X E v (u : X.G.P.W v)
  have b2 := norm_sigma_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have n1 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))
  have n2 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))
  have n3 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))))
  have n4 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))))
  constructor <;> nlinarith

theorem norm_sigma_alg (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ =
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (X.G.P.setting v).p_unif
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, (norm_unit X E v u).1, (norm_unit X E v u).2]

theorem norm_sigma (X : Sys p) (E : CEmb X.G) (v : X.Pl) (y : X.G.P.Qq v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v y))‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) y
  simp only [map_div₀, norm_div, norm_sigma_alg]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.Qq v) :
    ‖twG X E v s y‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  simp only [twG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  generalize s.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((X.G.P.σ v) ^ (n + 1)) y = X.G.P.σ v (((X.G.P.σ v) ^ n) y) := by rw [pow_succ']; rfl
    rw [e, norm_sigma, ih]

theorem prod_parity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if s.val % 2 = 1 then b else a) = (a * b) ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [Fin.prod_univ_eq_prod_range (fun i => if i % 2 = 1 then b else a) (m + m)]
  have : m + m = 2 * m := by ring
  rw [this, Nat.mul_div_cancel_left m (by norm_num)]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h0 : ¬ (2 * m) % 2 = 1 := by omega
    simp only [h1, h0, if_true, if_false]
    rw [mul_assoc]

theorem prod_parity_pos {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if IsOddPos s then b else a) = (a * b) ^ (n / 2) := by
  rw [← prod_parity a b n hn]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1
  · rw [if_pos h, if_pos (show IsOddPos s from h)]
  · rw [if_neg h, if_neg (show ¬ IsOddPos s from h)]

end GlobalTheory.TwU.NormOne

namespace GlobalTheory.TwU.NormOne

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have h : IsIntegral ℚ (TaylorLogMetric.embT D τ x) := (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom
  exact mem_algebraicClosure_iff.2 h.isAlgebraic

end GlobalTheory.TwU.NormOne


open GlobalTheory.TwU.NormOne in
theorem GlobalTheory.TwV.prod_embT_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  intro D _ hT _ _ _ _ _ _ u _ w hg _ _ H X _ std _ J S hPos ι hι z hz
  have hl : ∀ τ, ι (TaylorLogMetric.embT D τ z) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D τ z) := by
    intro τ
    rw [TaylorLogMetric.lamC, dite_eq_left (embT_mem_qbar D τ z)]
    exact hι ⟨_, embT_mem_qbar D τ z⟩
  rw [map_prod, norm_prod]
  simp only [hl]
  rw [← Fintype.prod_equiv (hT.gat_pos u w hg) (fun σ => ‖TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg σ) z)‖) _ (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  have hP : ∀ v s x, TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) =
      twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj x else x)) := hPos
  refine Finset.prod_eq_one fun v _ => ?_
  have hs : ∀ s : Fin ((sysS H X std).G.P.n' v),
      ‖twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj z else z))‖ =
        if IsOddPos s then ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v (D.host.conj z)))‖
        else ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v z))‖ := by
    intro s
    split_ifs <;> exact norm_twG _ _ _ _ _
  simp only [hP]
  refine (Finset.prod_congr rfl fun s _ => hs s).trans ?_
  rw [prod_parity_pos _ _ _ ((sysS H X std).G.P.setting v).even, ← norm_mul, ← map_mul, ← map_mul, ← map_mul, hz,
    map_one, map_one, map_one, norm_one, one_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.ScaleUnit

theorem norm_ltC_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  obtain ⟨-, hAt, -⟩ := S.curve
  obtain ⟨h1, h2, h3, hLam, hOk⟩ := hAt
  have hU : GL3Theta.IsModelU S.g.lam (TaylorLogMetric.lamOf D t.cc t.δ) S.g.C := hLam ▸ hOk.1
  have hu := (GlobalTheory.UnitModel.modelEx_holds D _ S.g.lam t.cc t.δ h1 h2 h3).2.2 S.g.C hU
  unfold ltC
  rw [norm_inv, norm_mul, hu, norm_wToC_unit, mul_one, inv_one]

end GlobalTheory.TwU.ScaleUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtension
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SerMap

theorem iteratedFDeriv_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => c * G z) α = c * TaylorLogMetric.taylor D G α := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    unfold TaylorLogMetric.taylor
    simp
  · unfold TaylorLogMetric.taylor
    have h := iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)
    simp only [smul_eq_mul] at h
    rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem padicSeries_const_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]),
    (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar →
    TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) →
    serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  intro D p _ lam ι hι a b K G s s' hs hK hKG
  ext α
  have hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α := by
    have : K = fun z => s' * G z := funext hKG
    rw [this, taylor_mul]
  have hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs (hK α)
  show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _
  rw [taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem, ← hι ⟨_, hmem⟩]
  show ι (s * TaylorLogMetric.taylor D K α) = _
  rw [hKt, ← mul_assoc, map_mul]
  rfl

end GlobalTheory.TwV.SerMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentity
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullback_contraction_scalars : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  intro m m' g g' k k' x x' A A' Δ Δ' n n' c c' hm hm' hg hg' hk hk' hx hx' hA hA' hΔ hΔ'
  simp only [mul_zpow, inv_zpow', zpow_neg, zpow_add₀ hΔ, zpow_add₀ hΔ', zpow_add₀ hA, zpow_add₀ hA', neg_add, mul_inv, inv_inv, div_eq_mul_inv]
  field_simp

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullbackScalar_ne_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La La' h1 h2
  have hj' : j + 1 ≤ D.R.m := hj
  have key := fun (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i) (hLb : ((sysS H X std).Pj i).IsLatTup Lb.2) =>
    _root_.GlobalTheory.TwV.mu_det_rat_y_lev J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj i hi (clsAt X H i Lb.1 Lb.2) (J.pt std i hi Lb)
      (d.gam i hi Lb) (d.mem i hi Lb) (d.kap i hi Lb) (d.eq i hi Lb hLb)
  have n1 := (key j (Nat.le_of_succ_le hj') La h1).2.2
  have n2 := (key (j + 1) hj' La' h2).2.2
  simp only [Dec.sP, dif_pos hj', Dec.chi]
  exact div_ne_zero (mul_ne_zero n1 (Units.ne_zero _)) (mul_ne_zero n2 (Units.ne_zero _))

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFrames
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem sum_pullMat_subBG_reframe : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  intro D p _ X E pos fd lam ι hι ρ hL e c j La La' he he' hdet x y
  classical
  have hs : ∀ q : D.host.E, star q = D.host.conj q := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hcc : ∀ q : D.host.E, D.host.conj (D.host.conj q) = q := fun q => D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
  have hconj : ∀ τ q, TaylorLogMetric.embT D τ (D.host.conj q) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ q) := fun τ q =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) q
  have hιe : ∀ τ q, ι (TaylorLogMetric.embT D τ q) = twG X E (pos.symm τ).1 (pos.symm τ).2
      (ρ _ (if IsOddPos (pos.symm τ).2 then D.host.conj q else q)) := by
    intro τ q
    have halg : TaylorLogMetric.embT D τ q ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) q).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
    have h2 := hL (pos.symm τ).1 (pos.symm τ).2 q
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h2
    rw [← h2]; unfold TaylorLogMetric.lamC; rw [dite_eq_left halg]; exact hι ⟨_, halg⟩
  have hinv : ∀ {n : ℕ} (v : X.Pl) (A : Matrix (Fin n) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin n) (X.G.P.Qq v)),
      A * star A = 1 → ((star A).map (ρ v) * M)⁻¹ = M⁻¹ * A.map (ρ v) := by
    intro n v A M h
    rw [Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero (ρ v)) (map_one (ρ v))]
  obtain ⟨τ, b0, a0⟩ := x
  obtain ⟨τ', b1, a1⟩ := y
  by_cases hxy : τ = τ'
  · subst hxy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [subBG, reframe, pullMat, ↓reduceIte]
      rw [hinv _ _ _ he, hinv _ _ _ he']
      by_cases hodd : IsOddPos (pos.symm τ).2
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
          first
            | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
            | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
          first
            | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
            | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · intro τ'' _ hne
      apply Finset.sum_eq_zero
      intro z _
      simp [pullMat, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [show subBG E pos (reframe fd ρ e) j La La' (τ, b0, a0) (τ', b1, a1) = 0 from if_neg hxy, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : τ = z.1
    · have h2 : z.1 ≠ τ' := fun h => hxy (h1.trans h)
      rw [show subBG E pos fd j La La' z (τ', b1, a1) = 0 from if_neg h2, mul_zero, mul_zero]
    · rw [show pullMat (e j La) (e (j + 1) La') (τ, b0, a0) z = 0 from if_neg h1, map_zero, zero_mul]

end GlobalTheory.TwV.DelB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAtStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | (intros; apply GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm good rat dgam one e0
  exact GlobalTheory.Port.site_labels_with_stepZero_classMap Gt c g u w hg Tw μ Z Fl ht hm good rat dgam one e0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtPStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  exact fun {D} X0 u w hg Tw μ Z Fl ht Gt =>
    @GlobalTheory.TwV.LbB.lbAtB_inTw D X0 u w hg Tw μ Z Fl ht Gt
end

