module

public import Mathlib
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.NumPt

theorem jet_real {f m r t b g dF R : ℝ} (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r) (hd0 : 0 ≤ dF)
    (ht : 11 ≤ t) (hf : f ≤ t) (hm : m ≤ t) (hr : r ≤ t) (hb : t ^ 7 ≤ b) (hd : dF ≤ f * r * (2 * (2 * b) + 1))
    (hR : R ≤ b) (hg : b ^ 8 ≤ g) :
    4 * dF + 4 ≤ g ∧ dF * (2 * Real.sqrt (2 * f * m)) < g ∧
      R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) / g ≤ 1 / 2500 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b := fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb
  have h100 : 100 ≤ b := by nlinarith [hp 2 (by norm_num)]
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hfr : f * r ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)
  have hfm : f * m ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have h5 : 5 * t ^ 2 ≤ b := by
    have : t ^ 3 = t * t ^ 2 := by ring
    nlinarith [hp 3 (by norm_num)]
  have hdb : dF ≤ b ^ 2 := by
    have h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b) := mul_le_mul hfr (by linarith) (by linarith) ht2
    nlinarith
  have hN0 : 0 ≤ 2 * f * m := by positivity
  have hN : 2 * f * m ≤ b := by nlinarith
  have hN3 : (2 * f * m) ^ 3 ≤ b := by
    have h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3 := pow_le_pow_left₀ hN0 (by linarith) 3
    have h2 : t ^ 7 = t * t ^ 6 := by ring
    have h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6 := by ring
    have h4 : 0 ≤ t ^ 6 := by positivity
    nlinarith
  have hrb : r ≤ b := hr.trans (by simpa using hp 1 (by norm_num))
  have hs : Real.sqrt (2 * f * m) ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1) := fun n => by
    rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)
  have e2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  have q2 := hq 2
  have q3 := hq 3
  have q4 := hq 4
  have q5 := hq 5
  have q6 := hq 6
  have q7 := hq 7
  norm_num at q2 q3 q4 q5 q6 q7
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b) :=
      mul_le_mul hdb (by linarith) (by positivity) (by positivity)
    have h2 : b ^ 2 * (2 * b) = 2 * b ^ 3 := by ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have h1 : r * (2 * f * m) ≤ b ^ 2 := by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)
    have h2 : dF ^ 2 ≤ b ^ 4 := by
      have := pow_le_pow_left₀ hd0 hdb 2
      rwa [← pow_mul] at this
    have h3 : R * (2 * f * m) ^ 3 ≤ b * b := mul_le_mul hR hN3 (by positivity) (by linarith)
    have h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4) :=
      mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    have h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6 := by ring
    linarith

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

theorem jetNum_of_sizes {D : D7} {L : SizeData₂ D} (S : SizesAt L) {dF : ℕ}
    (hd : (dF : ℝ) ≤ D.R.f * D.R.r * (2 * (2 * L.sc.b) + 1)) : JetNum D dF (1 / 2500) := by
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have a4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r := by unfold Ranks.r; omega
  have ht : (11 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 11 ≤ D.R.t)
  have hf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hr : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : D.host.rdE ≤ szCond L := by
    unfold szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : (1 : ℝ) ≤ szCond L := h1.trans hc
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b := le_trans sC hsb
  have hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b :=
    ((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'
  have hrd : D.host.rdE ^ 2 ≤ L.sc.b :=
    (((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'
  have hR : rr0 D ≤ L.sc.b := by
    have hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
    have e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
      unfold Formalism.BasicNotions.Host.rdE
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    unfold rr0
    rw [e]
    exact (div_le_self (by positivity) (by linarith)).trans hrd
  intro k
  have hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  obtain ⟨c1, c2, c3⟩ := jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hf hm hr hb hd hR hg
  exact ⟨by exact_mod_cast c1, c2, c3⟩

section Cols

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q :=
  _root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ

theorem two_mul_rank_le_nCol (Dw : Datum H) : 2 * (Dw.p + Dw.q) ≤ nCol Dw := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := mult_add_mult_conj Dw τ
  have hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw) := fun σ => by
    have := Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw))
      (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)
    rwa [Fintype.card_fin] at this
  have h1 := hle τ
  have h2 := hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)
  unfold nCol
  omega

end Cols

theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hL : 1 ≤ L.sc.L) (hf : 1 ≤ D.R.f) (hr : 1 ≤ D.R.r) :
    Real.log (D.host.g 0) + Real.log (D.host.g 1) ≤ (2 + 2 * P.CYL) * zBase L ^ 12 := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L := fun i => by
    have a := Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have := Real.log_two_lt_d9
    linarith
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hZ : L.sc.L ≤ zBase L := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')
  have hZ' : L.sc.L ≤ zBase L ^ 12 := hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))
  have := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])
  linarith [hg 0, hg 1]

end GlobalTheory.RefSum.NumPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

end BC

end GlobalTheory.JetIsotropic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CxCoh.CxMap

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

def pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : CxMap K K' where
  G := G
  a0 T := (m.a0 T).comp (K.M0.map (θ.app T))
  a1 T := (m.a1 T).comp (K.M1.map (θ.app T))
  a2 T := (m.a2 T).comp (K.M2.map (θ.app T))
  a3 T := (m.a3 T).comp (K.M3.map (θ.app T))
  compDegreeZero_natural {T T'} φ x := by
    change m.a0 T' (K.M0.map (θ.app T') (K.M0.map (G.map φ) x)) =
      K'.M0.map φ (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.M0.map_comp, θ.naturality, K.M0.map_comp, m.compDegreeZero_natural]
  compDegreeOne_natural {T T'} φ x := by
    change m.a1 T' (K.M1.map (θ.app T') (K.M1.map (G.map φ) x)) =
      K'.M1.map φ (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.M1.map_comp, θ.naturality, K.M1.map_comp, m.compDegreeOne_natural]
  compDegreeTwo_natural {T T'} φ x := by
    change m.a2 T' (K.M2.map (θ.app T') (K.M2.map (G.map φ) x)) =
      K'.M2.map φ (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.M2.map_comp, θ.naturality, K.M2.map_comp, m.compDegreeTwo_natural]
  comp_commutes_diffZero T x := by
    change m.a1 T (K.M1.map (θ.app T) (K.d0 _ x)) = K'.d0 T (m.a0 T (K.M0.map (θ.app T) x))
    rw [← K.diffZero_natural, m.comp_commutes_diffZero]
  comp_commutes_diffOne T x := by
    change m.a2 T (K.M2.map (θ.app T) (K.d1 _ x)) = K'.d1 T (m.a1 T (K.M1.map (θ.app T) x))
    rw [← K.diffOne_natural, m.comp_commutes_diffOne]
  comp_commutes_diffTwo T x := by
    change m.a3 T (K.M3.map (θ.app T) (K.d2 _ x)) = K'.d2 T (m.a2 T (K.M2.map (θ.app T) x))
    rw [← K.diffTwo_natural, m.comp_commutes_diffTwo]

theorem joined_pre (m : CxMap K K') {G : C' ⥤ C} (θ : G ⟶ m.G) : (m.pre θ).Joined m θ :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end GlobalTheory.CxCoh.CxMap

namespace GlobalTheory.PDForm

def pairB {D D' : Data} (Λ' : Lift D') {σ : D.R →+* D'.R} (φ : D'.X ⟶ D.X) {φ₀ : D'.X₀ ⟶ D.X₀}
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) : CxMap (KK D.κ D.t) ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)) :=
  (morMap m).comp ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L))

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section
namespace GlobalTheory.PrincSubring

def powLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : LB (Out.powObj A 8).left :=
  LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (Out.powPr A uv.1) (Out.powPr A uv.2)).left)
    fun uv => GlobalTheory.W8 uv.1 uv.2

def KerAlong {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (g : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A, IsTrivial (slice A P x) → x = 1

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => by
      have := hY.comm
      have := hY.smooth
      have := hY.proper
      have := hY.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change IsProper (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change GeometricallyConnected (pullback.snd Y.hom (U p).ι)
        infer_instance) hK

end GlobalTheory.KTrivSqZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyTraitU_of_kapF : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  intro κ hK V _ _ _ _ hcpl hfin D x G _ _ hG U w₀ hN y hy hvec σ hNz hMaps
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := _root_.GlobalTheory.CompleteDvrToComplex.exists_complete_closed_field V hcpl hfin
  obtain ⟨N, ν, hInt⟩ := _root_.GlobalTheory.IntGauge.exists_intN V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := _root_.GlobalTheory.KeyEven.ThetaNorm.main V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := hK V hcpl hfin D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact _root_.GlobalTheory.KeyEven.fractionRing_norm_one_unit V C hC _ e

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  first | exact @GlobalTheory.LevRingDesc.levRing_descent | exact GlobalTheory.LevRingDesc.levRing_descent | (intros; apply GlobalTheory.LevRingDesc.levRing_descent <;> assumption)
end

