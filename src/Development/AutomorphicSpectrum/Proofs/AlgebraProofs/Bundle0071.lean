module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelRootIndep
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0070
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.DualLattices.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerAction
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsNotMemSubConj
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem conj_not_trivial_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ m : Ideal (𝓞 E), m.IsMaximal → ∃ a : 𝓞 E, a - bar a ∉ m :=
  PositivityTheory.Xgf.exists_not_mem_sub_conj

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependent
section
namespace GlobalTheory.CompanionTheory.Ar.RootIndep

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main

end GlobalTheory.CompanionTheory.Ar.RootIndep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealPadicGeneratorLogNorm
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem ideal_local_generator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I :=
  @PositivityTheory.Xgf.ideal_padic_generator_log_norm

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
private theorem norm_intCast_padicAlgCl_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : PadicAlgCl p)‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap ℚ_[p] (PadicAlgCl p)) k, PadicAlgCl.norm_extends]
  exact Padic.norm_intCast_lt_one_iff

private theorem norm_intCast_cp_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : ℂ_[p])‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap (PadicAlgCl p) ℂ_[p]) k, ← PadicComplex.coe_eq,
    PadicComplex.norm_extends]
  exact norm_intCast_padicAlgCl_lt_one_iff_dvd p k

private theorem not_dvd_den_of_norm_le_one_padicAlgCl (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : ‖(q : PadicAlgCl p)‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hp : p.Prime := Fact.out
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hnum1 : ‖(q.num : PadicAlgCl p)‖ = 1 :=
    le_antisymm (IsUltrametricDist.norm_intCast_le_one _ _)
      (not_lt.mp fun h => hnum ((norm_intCast_padicAlgCl_lt_one_iff_dvd p _).mp h))
  have hden : ‖(q.den : PadicAlgCl p)‖ < 1 := by
    rw [← Int.cast_natCast, norm_intCast_padicAlgCl_lt_one_iff_dvd]
    exact Int.natCast_dvd_natCast.mpr hd
  have hden0 : 0 < ‖(q.den : PadicAlgCl p)‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
  rw [Rat.cast_def, norm_div, hnum1, div_le_iff₀ hden0, one_mul] at hq
  linarith

private theorem norm_multiset_prod_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (h a (by simp)) (norm_nonneg _) (ih fun y hy => h y (by simp [hy]))

private theorem norm_multiset_sum_le_one_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.sum‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (by simp)) (ih fun y hy => h y (by simp [hy])))

private theorem norm_esymm_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K)
    (h : ∀ y ∈ s, ‖y‖ ≤ 1) (k : ℕ) : ‖s.esymm k‖ ≤ 1 := by
  rw [Multiset.esymm]
  apply norm_multiset_sum_le_one_of_ultrametric
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  apply norm_multiset_prod_le_one_of_forall_norm_le_one
  intro z hz
  exact h z (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hz)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  intro E _ _ p x
  constructor
  · intro h
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
    have hroot : ∀ r ∈ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots,
        ‖r‖ ≤ 1 := by
      intro r hr
      have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl (p : ℕ)) := by
        refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, ?_⟩
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        exact (Polynomial.mem_roots'.mp hr).2
      rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (PadicAlgCl (p : ℕ)) x] at hr'
      obtain ⟨ψ, rfl⟩ := hr'
      have h1 := h ((algebraMap (PadicAlgCl (p : ℕ)) ℂ_[p]).comp (ψ : E →+* PadicAlgCl (p : ℕ)))
      rw [RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends] at h1
      exact h1
    have hcard : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots.card =
        ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    have hmon' : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).Monic := hmon.map _
    have hcoeff : ∀ k, ‖(((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ))‖ ≤ 1 := by
      intro k
      have e1 : (((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ)) =
          ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).coeff k := by
        rw [Polynomial.coeff_map]
        exact (eq_ratCast _ _).symm
      rw [e1]
      by_cases hk : k ≤ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree
      · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hk, hmon'.leadingCoeff, one_mul,
          norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_esymm_le_one_of_forall_norm_le_one _ hroot _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), norm_zero]
        exact zero_le_one
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ∏ k ∈ Finset.range ((minpoly ℚ x).natDegree + 1),
        ((minpoly ℚ x).coeff k).den := ⟨_, rfl⟩
    have hm : ¬ (p : ℕ) ∣ m := by
      rw [hmdef, Prime.dvd_finsetProd_iff p.2.prime]
      rintro ⟨k, -, hk⟩
      exact not_dvd_den_of_norm_le_one_padicAlgCl _ _ (hcoeff k) hk
    have hlift : Polynomial.C (m : ℚ) * minpoly ℚ x ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro k
      rw [Polynomial.coeff_C_mul]
      by_cases hk : k ≤ (minpoly ℚ x).natDegree
      · have hd : ((minpoly ℚ x).coeff k).den ∣ m := by
          rw [hmdef]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
        obtain ⟨t, ht⟩ := hd
        refine ⟨(t : ℤ) * ((minpoly ℚ x).coeff k).num, ?_⟩
        simp only [eq_intCast]
        rw [ht]
        push_cast
        rw [← Rat.den_mul_eq_num]
        ring
      · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), mul_zero,
          map_zero]⟩
    obtain ⟨g, hg⟩ := (Polynomial.mem_lifts _).mp hlift
    have hlc : g.leadingCoeff = (m : ℤ) := by
      have h1 := Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)) g
      rw [hg, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff, mul_one,
        eq_intCast] at h1
      exact_mod_cast h1.symm
    have hg0 : Polynomial.aeval x g = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ x g, hg, map_mul, Polynomial.aeval_C, minpoly.aeval,
        mul_zero]
    have hI := isIntegral_leadingCoeff_smul g x hg0
    rw [hlc] at hI
    have hI' : IsIntegral ℤ ((m : E) * x) := by
      simpa [zsmul_eq_mul, nsmul_eq_mul] using hI
    exact ⟨m, ⟨(m : E) * x, hI'⟩, hm, rfl⟩
  · rintro ⟨n, a, hpn, hna⟩ j
    have hn : ‖((n : ℕ) : ℂ_[p])‖ = 1 := by
      have h1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
      have h2 : ¬ ‖((n : ℕ) : ℂ_[p])‖ < 1 := by
        rw [← Int.cast_natCast, norm_intCast_cp_lt_one_iff_dvd]
        exact fun h => hpn (Int.natCast_dvd_natCast.mp h)
      linarith [not_lt.mp h2]
    have ha : ‖j (a : E)‖ ≤ 1 := by
      have h1 := GlobalTheory.CompanionTheory.Ar.HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) j a
      rw [NormedField.valuation_apply] at h1
      exact_mod_cast h1
    have hj : j ((n : E) * x) = (n : ℂ_[p]) * j x := by
      rw [map_mul, map_natCast]
    rw [hna] at hj
    calc ‖j x‖ = ‖(n : ℂ_[p])‖ * ‖j x‖ := by rw [hn, one_mul]
      _ = ‖(n : ℂ_[p]) * j x‖ := (norm_mul _ _).symm
      _ = ‖j (a : E)‖ := by rw [hj]
      _ ≤ 1 := ha
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR.Top

theorem pt_eq_one_of_g_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 :=
  GlobalTheory.T.trivial_polarized_abelian_point_eq_one

theorem exists_cp (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hpv : v (p : C) < 1) :
    ∃ cp : R, v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R)) := by
  have h1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) h1
  have hle : v c ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 < v c ^ (p - 1) := one_lt_pow₀ h h1.ne'
    rw [← map_pow, hc] at this
    exact absurd hpv (not_lt.2 this.le)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hle
  exact ⟨r, by rw [hr, ← v.map_pow, hc, map_natCast (algebraMap R C)]⟩

theorem hopf_carrier_g_zero {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) R (Nb p 0)) :
    AA.carrier = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  refine le_antisymm AA.le_int fun f hf => ?_
  obtain ⟨r, hr⟩ := hf default
  have : f = r • (1 : Nb p 0 → C) := by
    funext x
    rw [Subsingleton.elim x default, ← hr]
    simp [Algebra.smul_def]
  rw [this]
  exact AA.carrier.smul_mem r AA.one_mem

theorem torsFun_one_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) :
    torsFun C T (fun _ : Nb p 0 => (1 : sp (R₀ := R) R ⟶ G)) = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  obtain ⟨φ₀, hφ₀, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  ext f
  constructor
  · rintro ⟨a, ha⟩ x
    exact ⟨φ₀ a, (ha x φ₀ hφ₀).symm⟩
  · intro hf
    obtain ⟨r, hr⟩ := hf default
    refine ⟨algebraMap R T.A r, fun x φ _ => ?_⟩
    rw [Subsingleton.elim x default, ← hr, AlgHom.commutes]
    rfl

theorem main : HodgeTateDatumStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hcomp _ P
  haveI : IsLocalRing R := isLocal_of_integers hv
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : Fact ¬IsUnit (p : R) := ⟨fun hu => by
    have h1 := hv.one_of_isUnit hu
    rw [map_natCast] at h1
    rw [h1] at hp
    exact lt_irrefl _ hp⟩
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hcomp
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hT : Nonempty (TorsRep P.A p) :=
    _root_.GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple R p (Fact.out : p.Prime).one_le P.A P.L P.isAb P.isLB P.ample
  refine ⟨hT, ?_⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨cp, hcp⟩ := exists_cp p hv hp
    have hpne : v (algebraMap R C (p : R)) ≠ 0 := by
      rw [map_natCast]
      exact fun h => Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero ((Valuation.zero_iff v).1 h)
    have hplt : v (algebraMap R C (p : R)) < 1 := by rwa [map_natCast]
    have hS : HodgeTateSetting p v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp := by
      refine ⟨hv, hplt, hpne, hcp, ?_⟩
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        have h : ∀ (x : ℤ_[p]) (y : ℤ), sigE p ℤ (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
        rw [h, h, star_star]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    obtain ⟨H⟩ := GlobalTheory.ChF.htd_dim_zero p C v R hv ℤ cp
    rw [← hg] at H
    obtain ⟨hS', H', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    have h1 := pt_eq_one_of_g_zero R P hg
    revert H'
    rw [hg]
    intro H'
    refine ⟨cp, hS', H', fun _ => 1, ⟨?_, ?_, ?_⟩, fun T => ?_⟩
    · intro x y _
      let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
      exact Subsingleton.elim x y
    · intro x y
      exact (_root_.mul_one _).symm
    · intro z
      exact ⟨fun _ => ⟨0, (h1 z).symm⟩, fun _ => by rw [h1 z]; exact one_pow p⟩
    · rw [hopf_carrier_g_zero, torsFun_one_eq]
  · obtain ⟨F, X, hX⟩ := GlobalTheory.ChF.exists_nilChart R P.A P.g P.smoothDim
    obtain ⟨o⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GR.polAV_oAct_int R P
    have hα : ∀ a : ℤ, ∃ φ, Reads X X (o.act a) φ := fun a =>
      GlobalTheory.ChF.exists_reads R P.A P.A _ _ F.F F.F X X hX hX (o.act a) (o.hom a)
    choose α hα using hα
    obtain ⟨cp, hS, H, S, pt, -, -, -, -, -, hpt, hAA, -⟩ :=
      GlobalTheory.T.formal_group_chart_family p C v R hv P hg P.g rfl ℤ o F X hX α hα
    obtain ⟨hS', H', hAA', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    exact ⟨cp, hS', H', pt, hpt, fun T => by rw [hAA']; exact hAA T⟩

end GlobalTheory.CompanionTheory.Ar.GR.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SkewHermitianDiagonalizable
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem skewHermitian_congr_diag : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  exact @PositivityTheory.Xgf.skew_hermitian_diagonalizable

end GlobalTheory.CompanionTheory.CommAlg
end

