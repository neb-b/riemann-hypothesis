module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CompletedStalk

theorem essFiniteType_int_stalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.Poinc.CompletedStalk

theorem GlobalTheory.Poinc.CompletedStalk.exists_completion_unif : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧ ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  intro o' Ω _ _ _ hA S ρ hB M U₀ EE FinalForm hAdm hEE x hx
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hAdm.1.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _,
    isGrpPullback_pullback _ _, hL, hP⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem archimedeanBoundTotalConstant_nonneg_le_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → 0 ≤ GlobalTheory.EtaAn.p16 E r q m 5 1 ∧ GlobalTheory.EtaAn.p16 E r q m 5 1 ≤ 200000 * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * r * L) ^ 2 := by
  intro E _ _ _ r q m L hL hf hr hm hmr hq hρ lρ lF lR lq
  have key := GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size E r q m 1 L hL hf hr hm hmr hq hρ lρ lF lR lq (by simp; positivity)
  have hd : ((ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℕ) : ℝ) = 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * m := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.dstar; push_cast; ring
  have hfR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd2 : (2 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) := by rw [hd]; nlinarith
  have hRR : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) := by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ hρ
  have p3nn : 0 ≤ GlobalTheory.EtaAn.p3 E r q m := by
    unfold GlobalTheory.EtaAn.p3
    have hs := Real.sqrt_nonneg (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)
    apply mul_nonneg (Nat.cast_nonneg _)
    have a1 : 0 ≤ Real.log (1 + 6 * Real.sqrt (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)) :=
      Real.log_nonneg (by linarith)
    have a2 : 0 ≤ Real.log (2 * (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m :=
        one_le_pow₀ (by linarith)
      linarith
    have a3 : (0 : ℝ) ≤ ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_nonneg a3 a1
    linarith
  have hN : Real.log ((1 : ℕ) : ℝ) ≤ Real.log (((max 1 1 * 5 ^ (8 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2) : ℕ)) : ℝ) := by
    rw [Nat.cast_one, Real.log_one]; exact Real.log_natCast_nonneg _
  refine ⟨?_, le_trans ?_ key.2⟩
  · unfold GlobalTheory.EtaAn.p16
    have l5 : 0 ≤ Real.log ((5 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have l1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
    have hA : (1 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 := by
      push_cast; nlinarith
    have hB : (1 : ℝ) ≤ 4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2 := by nlinarith
    have a5 : 0 ≤ Real.log (((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 *
        (4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2)) :=
      Real.log_nonneg (by nlinarith)
    have t1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (r : ℝ) ^ 2) l5
    have t2 := mul_nonneg (by linarith : (0 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2) a5
    have t3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4) p3nn
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    rw [l1, zero_add]
    exact add_nonneg (mul_nonneg h5 (add_nonneg p3nn t1)) t2
  · unfold GlobalTheory.EtaAn.p16
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl (add_le_add hN le_rfl)) h5) le_rfl

theorem size_inequality_real : ∀ (rd c t b f r DF g0 g1 : ℝ), 1 ≤ rd → rd ≤ c → c ^ 36 * t ^ 150 ≤ Real.sqrt b → 11 ≤ t → 1 ≤ f → f ≤ t → 1 ≤ r → r ≤ t → 1 ≤ DF → DF ≤ b ^ 2 → b ^ 8 ≤ g0 → b ^ 8 ≤ g1 → (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ g0 * g1 := by
  intro rd c t b f r DF g0 g1 hrd hc hC ht hf1 hft hr1 hrt hD1 hDb hg0 hg1
  have ht1 : 1 ≤ t := by linarith
  have hc1 : 1 ≤ c := hrd.trans hc
  have hct : 1 ≤ c ^ 36 * t ^ 150 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ ht1)
  have hs1 : 1 ≤ Real.sqrt b := hct.trans hC
  have hb0 : 0 ≤ b := by
    by_contra h
    push_neg at h
    rw [Real.sqrt_eq_zero'.2 h.le] at hs1
    linarith
  have hbs := Real.sq_sqrt hb0
  have hb1 : 1 ≤ b := by nlinarith
  have hsb : Real.sqrt b ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hcb : c ^ 36 * t ^ 150 ≤ b := hC.trans hsb
  have ht7 : t ^ 7 ≤ b := by
    have e1 : t ^ 7 ≤ t ^ 150 := pow_le_pow_right₀ ht1 (by norm_num)
    have e2 : t ^ 150 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)
    linarith
  have hR : (rd ^ 7) ^ 4 ≤ b := by
    have e1 : (rd ^ 7) ^ 4 ≤ c ^ 28 := by rw [← pow_mul]; exact pow_le_pow_left₀ (by linarith) hc 28
    have e2 : c ^ 28 ≤ c ^ 36 := pow_le_pow_right₀ hc1 (by norm_num)
    have e3 : c ^ 36 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    linarith
  have ht2 : t ^ 2 ≤ t ^ 7 := pow_le_pow_right₀ ht1 (by norm_num)
  have htt : t ≤ t ^ 7 := le_self_pow₀ ht1 (by norm_num)
  have h180 : 180 ≤ b := by
    have : (11 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7
    norm_num at this
    linarith
  have hfr : f * r ≤ b := by nlinarith
  have hrb : r ≤ b := by linarith
  have hY : 90 * (f * r + DF) ≤ 180 * b ^ 2 := by nlinarith
  have hg : b ^ 16 ≤ g0 * g1 := by
    have := mul_le_mul hg0 hg1 (by positivity) (by linarith [one_le_pow₀ (M₀ := ℝ) hb1 (n := 8)])
    rw [← pow_add] at this
    exact this
  have e1 : (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ b * (180 * b ^ 2) * b ^ 2 * b := by
    have h0 : 0 ≤ (rd ^ 7) ^ 4 := by positivity
    have := mul_le_mul hR hY (by positivity) (by linarith)
    have := mul_le_mul this hDb (by linarith) (by positivity)
    exact mul_le_mul this hrb (by linarith) (by positivity)
  have e2 : b * (180 * b ^ 2) * b ^ 2 * b = 180 * b ^ 6 := by ring
  have e3 : 180 * b ^ 6 ≤ b ^ 16 := by
    have : b ^ 16 = b ^ 10 * b ^ 6 := by ring
    have h10 : b ≤ b ^ 10 := le_self_pow₀ hb1 (by norm_num)
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem sqrt_lt_th_real (q : ℕ) (M f R0 RR b s : ℝ) (hq : 1 ≤ q) (hb : 0 < b) (hM : (q : ℝ) * b ≤ M)
    (hf : 1 ≤ f) (hR : 1 ≤ R0 ^ 2) (hRR : 1 ≤ RR) (hs : M * s < b) :
    Real.sqrt s < Real.sqrt (f * R0 ^ 2 * RR ^ 3 / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hRR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hRR
  have h1 : 1 ≤ f * R0 ^ 2 * RR ^ 3 := by
    have := mul_le_mul hf hR zero_le_one (by linarith)
    nlinarith
  have hpos : 0 < f * R0 ^ 2 * RR ^ 3 / q := by positivity
  rcases le_or_gt s 0 with h0 | h0
  · rw [Real.sqrt_eq_zero'.2 h0]; exact Real.sqrt_pos.2 hpos
  · apply Real.sqrt_lt_sqrt h0.le
    rw [lt_div_iff₀ hq0]
    have : (q : ℝ) * b * s ≤ M * s := mul_le_mul_of_nonneg_right hM h0.le
    nlinarith

theorem level_ge {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {x : ℝ} {hx : Fm.x1 < x} {ι : Fm.Ix x} (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hL : 1 ≤ (Fm.L x ι).sc.L) :
    (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    congr 1
    exact p.fw.laws.toLawsM.pins.2.1.1
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have he : 3 * (Fm.L x ι).sc.L / Real.log 3 < (expL (Fm.L x ι).sc.L : ℝ) + 1 := Nat.lt_floor_add_one _
  have he' : (Fm.L x ι).sc.L ≤ (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 := by
    rw [div_lt_iff₀ hlog3p] at he
    nlinarith
  have hb : (Fm.L x ι).sc.b ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := by
    unfold Formalism.BasicNotions.Scale.b
    calc Real.exp (Fm.L x ι).sc.L ≤ Real.exp ((expL (Fm.L x ι).sc.L : ℝ) * Real.log 3) := Real.exp_le_exp.2 he'
      _ = (3 : ℝ) ^ expL (Fm.L x ι).sc.L := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
      _ ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [hM]
  push_cast
  exact mul_le_mul_of_nonneg_left hb (by positivity)


end GlobalTheory.ThetaSizeBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PullAction

section
open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_lift_end (h : IsGrpPullback G' G f φ) (u : G ⟶ G) [IsMonHom u] :
    ∃ v : G' ⟶ G', IsMonHom v ∧ v.left ≫ φ = φ ≫ u.left := by
  let v : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w u, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hv : v.left ≫ φ = φ ≫ u.left := h.1.lift_fst _ _ _
  have inj : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w x = pushPt h.1.w y → x = y := fun T x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  have pa : ∀ (T : Over S') (x : T ⟶ G'), pushPt h.1.w (x ≫ v) = pushPt h.1.w x ≫ u := fun T x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hv, Category.assoc])
  have pm : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have p1 : ∀ (T : Over S'), pushPt h.1.w (1 : T ⟶ G') = 1 := fun T => by
    have := pm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hm : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ v = (x ≫ v) * (y ≫ v) := fun T x y => inj T _ _ (by
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  have h1 : ∀ (T : Over S'), (1 : T ⟶ G') ≫ v = 1 := fun T => inj T _ _ (by
    rw [pa, p1, MonObj.one_comp])
  refine ⟨v, ⟨?_, ?_⟩, hv⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := hm (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

end

theorem exists_action_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  intro E _ _ _ H Dw l Xo c W w G₀ _ β₀ hβ
  have key : ∀ a : 𝓞 E, ∃ v : G₀ ⟶ G₀, IsMonHom v ∧ v.left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left := fun a =>
    haveI := Xo.univ.t.act.hom a
    exists_lift_end hβ _
  choose f₀ hf₀ using key
  refine ⟨f₀, hf₀, fun T x tT mm => ?_⟩
  have hp := hβ.1
  let γ : tT.G.left ⟶ G₀.left := hp.lift mm.φ (tT.G.hom ≫ x)
    (mm.cart.1.w.trans (by simp only [Category.assoc]))
  have hγ : γ ≫ β₀ = mm.φ := hp.lift_fst _ _ _
  have hw : γ ≫ G₀.hom = tT.G.hom ≫ x := hp.lift_snd _ _ _
  have hL : LBIso tT.PP.L (Xo.univ.t.PP.L.pull mm.φ) := mm.lin.imp fun _ h => h.1
  have hU := Xo.univ.t.PP.isLB
  refine ⟨γ, hβ.cancel (by rw [hγ, ← Category.assoc]; exact mm.cart) hw, hγ,
    LBIso.trans tT.PP.isLB (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
      (GlobalTheory.GenSpread.lbIso_pull_pull hU γ hγ.symm), fun a => ?_⟩
  apply hp.hom_ext
  · rw [Category.assoc, hγ, mm.act, Category.assoc γ, (hf₀ a).2, ← Category.assoc γ, hγ]
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.PullAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc.ChartAt

theorem spec_ext_of_isFractionRing {A K T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing T] (h₁ h₂ : Sp T ⟶ Sp K) (e : h₁ ≫ spMap (algebraMap A K) = h₂ ≫ spMap (algebraMap A K)) : h₁ = h₂ := by
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective h₁
  obtain ⟨g₂, rfl⟩ := Spec.map_surjective h₂
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (nonZeroDivisors A) e'

theorem exists_int_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {cf : Coeff l} (C : UCompact Xo cf) {a : C.o} (ha : a ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ a ∣ (n : C.o) := by
  haveI := C.ded
  have h1 : IsAlgebraic ℚ (C.b a) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 : IsAlgebraic ℤ (C.b a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ cf.F).2 h1
  have h3 : IsAlgebraic ℤ a := (isAlgebraic_algHom_iff C.b.toIntAlgHom C.inj).1 h2
  have h4 := Ideal.comap_ne_bot_of_algebraic_mem ha (Ideal.mem_span_singleton_self a) h3
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨n, hn0, ?_⟩
  have := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hn)
  simpa using this

end GlobalTheory.UPoinc.ChartAt

namespace GlobalTheory.UPoinc.ChartAt

theorem exists_affine_chart_ratLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw l Xo cf C X w hw
  haveI := X.ar.char
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  set V' : X.M.Z.Opens := X.π ⁻¹ᵁ ⟨V, hVo⟩ with hV'def
  have hwV : w ∈ V' := by
    obtain ⟨x, hx⟩ := hw
    show X.π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) (U := V') hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  set R₀ := X.M.ringOn U with hR₀
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ X.π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : cf.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o cf.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o cf.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hU, hwU, ?_⟩
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  have hfst : spMap (ratHull R₀).val.toRingHom ≫ g = X.uΩ ≫ C.i := by
    show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ X.π = _
    rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf, X.comp]
    simp only [USetup.uΩ, Category.assoc]
  rw [← cancel_mono C.iF, Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hfst]
    simp only [UCompact.i, Category.assoc]
  · have key : spMap (ratHull R₀).val.toRingHom ≫ g' ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b =
        X.uΩ ≫ C.iF ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b := by
      rw [← pullback.condition, ← Category.assoc g', pullback.lift_fst, reassoc_of% hfst]
      simp only [UCompact.i, Category.assoc]
    exact spec_ext_of_isFractionRing (A := C.o) _ _ (by simpa only [Category.assoc] using key)

end GlobalTheory.UPoinc.ChartAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  first | exact @GlobalTheory.Mum.RigScale.exists_rig_rescale | exact GlobalTheory.Mum.RigScale.exists_rig_rescale | (intros; apply GlobalTheory.Mum.RigScale.exists_rig_rescale <;> assumption)
end

