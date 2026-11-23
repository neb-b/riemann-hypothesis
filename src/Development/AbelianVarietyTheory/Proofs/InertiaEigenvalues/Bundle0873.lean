module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventually
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LevelBelowStarBound.QdSmall

theorem qd_lt_lStar_at {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L)
    (hy : Real.exp 1 ≤ L.sc.x ^ (L.sc.eps / 3)) :
    (D.host.q : ℝ) < LevelStarExponents.lStar L ∧ (D.host.d : ℝ) < LevelStarExponents.lStar L ∧ ∀ p ∈ D.host.small, (p : ℝ) < LevelStarExponents.lStar L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  set y := L.sc.x ^ (L.sc.eps / 3) with hydef
  have hL : L.sc.L = y ^ 3 := by
    unfold Scale.L
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
  have hy2 : 2 < y := lt_of_lt_of_le he2 hy

  have hkey : L.sc.L / 72 < L.sc.L - y := by
    rw [hL]
    have hy0 : 0 ≤ y := by linarith
    have h4 : 4 ≤ y ^ 2 := by nlinarith
    have : 4 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h4 hy0]
    nlinarith

  have hb' : Real.exp (L.sc.L - y) ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    rw [← hydef, Real.exp_sub, mul_div_assoc]
    have : 0 ≤ Real.exp L.sc.L / Real.exp y := by positivity
    nlinarith

  have hn1 : (1 : ℝ) ≤ D.R.n := Formalism.MainNotions.TwistedPlaces.n_ge_one D
  have ht1 : (1 : ℝ) ≤ D.R.t := Formalism.MainNotions.TwistedPlaces.t_ge_one D
  have hc := P.condE_le
  have hc0 : (0 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by positivity
  have hc36 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ Real.exp (L.sc.L / 72) ^ 36 := by
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
    have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) h1
    have h3 : L.sc.b ^ ((1 : ℝ) / 2) = Real.exp (L.sc.L / 72) ^ 36 := by
      unfold Scale.b
      rw [← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    linarith
  have hcE : (LevelStarExponents.condE D : ℝ) ≤ Real.exp (L.sc.L / 72) :=
    (pow_le_pow_iff_left₀ hc0 (Real.exp_pos _).le (by norm_num)).1 hc36
  have hlt : (LevelStarExponents.condE D : ℝ) < L.sc.b' :=
    lt_of_le_of_lt hcE (lt_of_lt_of_le (Real.exp_lt_exp.2 hkey) hb')
  have hstar : L.sc.b' < LevelStarExponents.lStar L := Formalism.MainNotions.TwistedPlaces.lStar_gt L P

  obtain ⟨hq, hd⟩ := P.qd_pow
  have hxp : 0 < L.sc.x ^ (2 * L.Ct + 5) := Real.rpow_pos_of_pos hx0 _
  have hq0 : 1 ≤ D.host.q := by
    have : (0 : ℝ) < D.host.q := lt_trans hxp hq
    exact_mod_cast this
  have hd0 : 1 ≤ D.host.d := by
    have : (0 : ℝ) < D.host.d := lt_trans hxp hd
    exact_mod_cast this
  have hS0 : 1 ≤ D.host.QS := D.host.QS_pos
  have hcv : LevelStarExponents.condE D = D.host.QS * D.host.q * D.host.d := rfl
  have hqC : D.host.q ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hdC : D.host.d ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.d = 1 * 1 * D.host.d := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hSC : D.host.QS ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.QS = D.host.QS * 1 * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hqC' : (D.host.q : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hqC
  have hdC' : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hdC
  refine ⟨by linarith, by linarith, fun p hp => ?_⟩
  have hpC : (p : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast (Nat.le_of_mem_primeFactors hp).trans hSC
  linarith

theorem qd_lt_lStar : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  intro eps Fm
  refine ⟨Real.exp (3 / eps), fun x hx0 hx a => ?_⟩
  apply qd_lt_lStar_at (Fm.L x a) (Fm.params x hx a)
  have hX := Fm.L_x x a hx
  have hE := Fm.L_eps x a
  have hpos : 0 < eps := hE ▸ (Fm.L x a).sc.eps_pos
  rw [hX, hE]
  have h3 : 0 < eps / 3 := by positivity
  calc Real.exp 1 = Real.exp (3 / eps) ^ (eps / 3) := by
        rw [← Real.exp_mul]; congr 1; field_simp
    _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (Real.exp_pos _).le hx0 h3.le

end GlobalTheory.LevelBelowStarBound.QdSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBound
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

open scoped ENNReal

namespace GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

open GlobalTheory.IndefiniteRowSideFullHecke

theorem congBound_of_rational : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  intro D i π ρ hπ hζ h
  classical
  obtain ⟨he0, het⟩ := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i
  refine (GlobalTheory.Proof.QuotientLengthInfimum.conclusion_iff D i π ρ).2 ?_
  by_cases hs : Br.sFin D.loc D.nbr i (fun _ => ρ) π
  swap
  · have h1 : SelmerSumLargePrime.selLen D i ρ π = ⊤ := not_lt_top_iff.mp hs
    rw [h1]; simp
  by_cases hsh : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤
  swap
  · push Not at hsh
    obtain ⟨k, hk, hk'⟩ := hsh
    have h1 : SelmerSumLargePrime.shaSum D i = ⊤ := by
      unfold SelmerSumLargePrime.shaSum
      refine top_le_iff.mp (le_trans hk' ?_)
      exact Finset.single_le_sum (f := fun e : ℕ => Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ))
        (fun _ _ => zero_le) hk
    rw [h1, ENat.mul_top he0]; simp
  have hr := h hs hsh
  have hc : SelmerSumLargePrime.ccLen D i π ≠ ⊤ := by
    unfold SelmerSumLargePrime.ccLen
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.vcc_ne_top _ (D.nd.T_sep i) _ _ hπ
  have hs' : SelmerSumLargePrime.selLen D i ρ π ≠ ⊤ := hs.ne
  have hq : ∀ P ∈ D.nd.Q i,
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1}) ≠ ⊤ := by
    intro P hP
    have h0 : SelmerSumLargePrime.zetaP D i P - 1 ≠ 0 := by
      rw [← GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq, BaseSizes.zetaP_eq D i P hP]
      exact sub_ne_zero.mpr (hζ P hP)
    exact Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero h0))
  have hrow : ∀ k ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) k : ℚ) =
      ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat : ℚ) := fun k hk =>
    D.nd.sha_eq _ k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 _
      (ENat.natCast_toNat (hsh k hk).ne).symm
  have hlq : ∀ P ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i P - 1}) =
      ((Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat : ℚ) /
        ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    intro P hP
    rw [← BaseSizes.zetaP_eq D i P hP, GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq]
    rfl
  have hv : D.nd.vcc i π = ((SelmerSumLargePrime.ccLen D i π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  have hsp : Br.sPi D.loc D.nbr i (fun _ => ρ) π =
      ((SelmerSumLargePrime.selLen D i ρ π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  rw [hv, hsp, Finset.sum_congr rfl hrow, Finset.sum_congr rfl hlq, ← Finset.sum_div] at hr
  have hE0 : (0 : ℚ) < ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    have : (SelmerSumLargePrime.ramLen D i).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; tauto
    exact_mod_cast Nat.pos_of_ne_zero this
  set E := (SelmerSumLargePrime.ramLen D i).toNat with hEdef
  set c := (SelmerSumLargePrime.ccLen D i π).toNat
  set s := (SelmerSumLargePrime.selLen D i ρ π).toNat
  set A := ∑ k ∈ Finset.Ioo 0 D.R.t, (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat with hA
  set B := ∑ P ∈ D.nd.Q i,
    (Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat with hB
  set v := padicValNat (D.nd.l i) (hE D.host)
  have key : (c : ℚ) ≤ s + E * A + E * v + D.R.t * B := by
    have h2 : ((s : ℚ) / E + (A : ℚ) + (v : ℚ) + (D.R.t : ℚ) * ((B : ℚ) / E)) * E =
        s + E * A + E * v + D.R.t * B := by
      field_simp
    rw [← h2, ← div_le_iff₀ hE0]
    push_cast [hA, hB]
    exact hr
  have knat : c ≤ s + E * A + E * v + D.R.t * B := by exact_mod_cast key
  have hsum : SelmerSumLargePrime.shaSum D i = (A : ℕ∞) := by
    unfold SelmerSumLargePrime.shaSum
    rw [hA, Nat.cast_sum]
    exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hsh k hk).ne).symm
  have htw : SelmerSumLargePrime.twistLen D i = ((D.R.t * B : ℕ) : ℕ∞) := by
    unfold SelmerSumLargePrime.twistLen
    rw [hB, Nat.cast_mul, Nat.cast_sum]
    exact congrArg _ (Finset.sum_congr rfl fun P hP => (ENat.natCast_toNat (hq P hP)).symm)
  rw [hsum, htw, ← ENat.natCast_toNat hc, ← ENat.natCast_toNat hs', ← ENat.natCast_toNat het]
  exact_mod_cast knat

end GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverConstantsUniqueOnDictionaryComponents
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries


set_option maxHeartbeats 1000000 in
theorem cc_unique_of_pinned : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ c : C.U₂.Comp → ℂ, (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → (∀ a, Dom a (κ i).n → ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n) → ∀ h, C.cc₂ (C.dict₂ h).1 = c (C.dict₂ h).1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT _ _ _ _ _ _ i _ _ C hC c hP hP' h
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hr, -⟩ := hT.modelW _ hj _ hσ

  obtain ⟨a, ha, hk⟩ := _root_.GlobalTheory.CoverNZ.exists_sec_ne_zero_each_comp D T hT _ hj _ hσ (κ i).n (κ i).n_even
  set k₀ := (T.dict ((i : ℕ) + 1) T.σ₀ h).1 with hk₀
  obtain ⟨f, hf, x, hx, hne⟩ := hk k₀
  have hU := hT.unf _ hj _ hσ
  have hS := hU.2.2.2.2.1 a _ ha f hf k₀

  obtain ⟨x₁, b, hb, ho, hx₁⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E _ _ _ _
    ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).Gm_herm).1 x hx
  have hne₁ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ x₁ ≠ 0 := by
    rw [hx₁, hS.2.1 x hx b hb]
    exact mul_ne_zero (GlobalTheory.CoverIndep.bchar_ne_zero' _ hb) hne
  have ho' : GlobalTheory.CoverDescSpan.IsOrthFr ((T.U ((i : ℕ) + 1) T.σ₀).X k₀) x₁ := ho

  obtain ⟨u, hu, hxu⟩ := (GlobalTheory.CoverDescSpan.base_orth hT hj hσ hr hθ h).2 x₁ ho'
  obtain ⟨γ, hγ, hdu⟩ := GlobalTheory.CoverDescSpan.base_real hT hj hσ hr hθ h u hu
  rw [← hxu] at hdu
  have hne₂ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
      (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2 ≠ 0 := by
    rw [hdu]
    show rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ (lact γ x₁) ≠ 0
    rw [hS.2.2 γ hγ x₁ ho'.mem_dom]
    refine mul_ne_zero ?_ hne₁
    obtain ⟨N, hN, hN1⟩ := ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).χ_fin (laU (T.U ((i : ℕ) + 1) T.σ₀) a (κ i).n k₀)
    intro h0
    have := hN1 γ hγ
    rw [h0, zero_pow hN.ne'] at this
    exact zero_ne_one this
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hphi : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) ≠ 0 := by
    have eb : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
        ((T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
          rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
            (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2) := rfl
    rw [eb]
    refine mul_ne_zero hl (mul_ne_zero (mul_ne_zero ?_ ?_) hne₂)
    · exact norm_ne_zero_iff.1 (by rw [hT.cUnit _ hj _ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal _ hj _ hσ).norm]; exact one_ne_zero)

  have hcomp : (C.dict₂ (h * u)).1 = (C.dict₂ h).1 := by
    have := (GlobalTheory.CoverDescSpan.cover_real hT hj hσ hr hθ C hC h 1 u (one_mem _) hu).1
    rwa [one_mul] at this

  obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.CovPull.exists_pull D T hT _ hj _ hσ C hC.1 a (κ i).n f hf
  have e1 := congrFun ((hP a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have e2 := congrFun ((hP' a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have ec : C.rd a f₂ (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((C.cc₂ (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  have ec' : ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).rd a f₂ (h * u) =
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((c (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  rw [ec] at e1
  rw [ec'] at e2
  have hne₃ := e1 ▸ hphi
  have hm : T.mu ((i : ℕ) + 1) T.σ₀ (h * u) ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have hX : rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2 ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have key := e1.trans e2.symm
  rw [← hcomp]
  have k2 : C.cc₂ (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) =
      c (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := by
    linear_combination key
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hl hm) hX) k2

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem wAll_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F :=
  fun D HW F Cm =>
    _root_.GlobalTheory.WachHyp.hypW_crystalline D HW F Cm (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1 (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).2 (GlobalTheory.crysOnCond_all D HW F)

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeriesStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsMod
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
namespace GlobalTheory.CycGen

open Pointwise

theorem fix_of_unram {E Ω : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field Ω] [Algebra E Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A) (x : E) :
    σ (algebraMap E Ω x) = algebraMap E Ω x := by
  have : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set τ : E ≃ₐ[ℚ] E := AlgEquiv.restrictNormalHom E σ with hτdef
  have hcomm : ∀ y : E, algebraMap E Ω (τ y) = σ (algebraMap E Ω y) := fun y =>
    AlgEquiv.restrictNormal_commutes σ E y
  have hin : τ ∈ Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal := by
    intro y
    show τ • y - y ∈ w.asIdeal
    rw [← hw]
    have hy : algebraMap E Ω (y : E) ∈ A :=
      ReciprocityTheory.Gal.mem_of_isIntegral_int A ((y.2).map (IsScalarTower.toAlgHom ℤ E Ω))
    have h := hσ.2 (algebraMap E Ω (y : E)) ((A.valuation_le_one_iff _).mpr hy)
    have e : ((τ • y - y : 𝓞 E) : E) = τ y - y := rfl
    rw [e, map_sub, hcomm]
    exact h
  have hcard : Nat.card (Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal) = 1 := by
    have := w.isPrime
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal (E ≃ₐ[ℚ] E), he]
  have h1 : τ = 1 := by
    have := (Subgroup.card_eq_one.mp hcard)
    have h2 : τ ∈ (⊥ : Subgroup (E ≃ₐ[ℚ] E)) := this ▸ hin
    exact Subgroup.mem_bot.mp h2
  rw [← hcomm, h1]
  rfl

end GlobalTheory.CycGen

namespace GlobalTheory.CycGen

theorem exists_unit_gen (l : ℕ) [Fact l.Prime] :
    ∃ v : ℤ_[l]ˣ, orderOf (PadicInt.toZMod (v : ℤ_[l])) = l - 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l])
  have hb : PadicInt.toZMod b = (a : ZMod l) := by
    simp only [b, map_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit b := by
    by_contra hn
    have hm : b ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hb] at hm
    exact a.ne_zero hm
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hb, orderOf_units, orderOf_eq_card_of_forall_mem_zpowers ha,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  intro R H what₂ N i hram
  obtain ⟨w, hw⟩ := GlobalTheory.TameFixedLift.exists_place H.E (N.l i)
  refine ⟨w, hw, ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have := H.hostE_isGalois
  obtain ⟨v, hv⟩ := exists_unit_gen (N.l i)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective N.Om (N.l i) (N.plOm.1 w) hA v
  obtain ⟨g, hg, hc⟩ := GlobalTheory.TameFixedLift.transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (fix_of_unram (N.plOm.1 w) w (N.plOm.2 w) (hram w hw) σ hσ)
  exact ⟨g, hg, by rw [hc, hσv, hv]⟩

end GlobalTheory.CycGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariantStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_parahoric_invariant : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  first | exact @GlobalTheory.JacTypeVec.exists_subquot_typeVec | exact GlobalTheory.JacTypeVec.exists_subquot_typeVec | (intros; apply GlobalTheory.JacTypeVec.exists_subquot_typeVec <;> assumption)
end

