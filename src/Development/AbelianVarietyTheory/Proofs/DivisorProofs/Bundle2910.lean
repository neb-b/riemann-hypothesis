module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour
section
namespace GlobalTheory.LiftFour

theorem abelianLifting_of_four :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a c d e => _root_.GlobalTheory.SqLift.abelianLifting_of_known_theorems a _root_.GlobalTheory.CubeTop.cubeTheorem c d e

end GlobalTheory.LiftFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMovesStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_trace_unitBlock_trivial_of_moves : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  first | exact @GlobalTheory.CosetOrth.Pairing.char_trace_eq_one | exact GlobalTheory.CosetOrth.Pairing.char_trace_eq_one | (intros; apply GlobalTheory.CosetOrth.Pairing.char_trace_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_ample_pos : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A B n hdim c d hc hd f hf
  obtain ⟨m, M, hM, s, hm, hcls, hne, horig⟩ := GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin K A B f d hd hf
  have htop : Out.nonzeroLocus s ≠ ⊤ := by
    intro h
    apply horig
    rw [h]
    trivial
  have hpos := _root_.GlobalTheory.AV.EffPos.inter_cons_pos K A n hdim c hc M hM s hne htop
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hdim])
  set x := CechPic.pull f.hom.left d
  have hcons : (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left)
      = Function.update (Fin.cons x (fun _ : Fin n => c)) 0 ((m : ℤ) • x) := by
    rw [hcls]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [natCast_zsmul]
    · simp [Function.update, Fin.succ_ne_zero]
  rw [← hΦ, hcons, Φ.map_update_smul, Fin.update_cons_zero, smul_eq_mul] at hpos
  rw [← hΦ]
  exact pos_of_mul_pos_right hpos (by simpa using Int.ofNat_nonneg m)

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpec
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem appLE_ι_appLE_eq_secMap : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  intro X T p U O hO V e r
  have hU : IsAffineOpen U.1 := U.2
  have key : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((p ∣_ U.1) ≫ hU.isoSpec.hom).appLE ⊤ V (by simp) =
      p.appLE U.1 O hO ≫ (p ⁻¹ᵁ U.1).ι.appLE O V e := by
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Scheme.Hom.appTop ((p ∣_ U.1) ≫ hU.isoSpec.hom) ≫
      (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change U.1.topIso.inv ≫ (p ∣_ U.1).appLE ⊤ V (show V ≤ (p ∣_ U.1) ⁻¹ᵁ ⊤ from fun _ _ => trivial) = _
    rw [morphismRestrict_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact (p.map_appLE _ _).trans (p.appLE_map _ _).symm
  exact (congrArg (fun f => f.hom r) key).symm

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  first | exact @GlobalTheory.MixHt.archRecip_of_principalisation | exact GlobalTheory.MixHt.archRecip_of_principalisation | (intros; apply GlobalTheory.MixHt.archRecip_of_principalisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithLogSmallSectionsUpperBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (_root_.GlobalTheory.KleimanNef.htNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := _root_.GlobalTheory.HSNef.gdeg_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply _root_.GlobalTheory.HSNef.smallFam_pair_tens k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := _root_.GlobalTheory.HSNefCore.key_ineq hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := _root_.GlobalTheory.HSNef.bl_finite k X p D hX P 1 0 1
  exact _root_.GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveIndep

variable {Y : Scheme.{0}} [IsIntegral Y] {L : LB Y}

theorem exists_ratio (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') : ∃ f : Y.functionFieldˣ, ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f := by
  obtain ⟨i₀, h₀⟩ := exists_chart hL (genericPoint Y)
  refine ⟨(r i₀)⁻¹ * r' i₀, fun i hi => Units.ext ?_⟩
  have e := hr i i₀ ⟨hi, h₀⟩
  have e' := hr' i i₀ ⟨hi, h₀⟩
  have h0 : (r i₀ : Y.functionField) ≠ 0 := (r i₀).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e', e]
  field_simp

theorem div_eq_add_principal (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') (f : Y.functionFieldˣ) (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) :
    divOfRatSec hL hr' = divOfRatSec hL hr + CartierDiv.principal f :=
  (presents_divOfRatSec hL hr').unique ⟨hL, hr', fun i x hx => by
    rw [hf i (gen_mem hx)]
    exact ((presents_divOfRatSec hL hr).add_principal f).isEqn i x hx⟩

theorem mult_eq_add_ord [IsLocallyNoetherian Y] (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hr' : IsRatSec L r') (f : Y.functionFieldˣ)
    (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) (z : Y) :
    (divOfRatSec hL hr').mult z = (divOfRatSec hL hr).mult z + Scheme.ord (f : Y.functionField) z := by
  rw [div_eq_add_principal hL hr hr' f hf, CartierDiv.mult_add,
    (CartierDiv.isEqn_principal f z).mult_eq]

end GlobalTheory.CurveIndep

namespace GlobalTheory.CurveIndep


open Classical in
theorem mixArch_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    (L : Fin 0 → HermLB q) (N : HermLB q) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r) :
    mixArch L N hr = (HermLB.triv q).archInt N 0 hr := by
  have h (n : Fin 0 → ℤ) : (comb L n).archInt N 0 hr = (HermLB.triv q).archInt N 0 hr := by
    have e : comb L n = HermLB.triv q := by simp [comb]
    rw [e]
  have e (S : Finset (Fin 0)) : S.card = 0 := by simp [Subsingleton.elim S ∅]
  simp [mixArch, FibreProj.pol, h, e]

theorem archInt_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  intro k _ Y _ _ q hA hd N L r hr r' hr'
  obtain ⟨f, hf⟩ := exists_ratio N.isLB hr hr'
  have := hA.isNoetherian
  set c : Y → ℝ := fun z => Real.log (Nat.card (Y.residueField z)) with hc
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * c z).Finite :=
    (CartierDiv.finite_support_mult D).subset fun z hz h0 => hz (by simp [h0])
  have hord (z : Y) : Scheme.ord (f : Y.functionField) z = (CartierDiv.principal f).mult z :=
    ((CartierDiv.isEqn_principal f z).mult_eq).symm
  have hsum : ∑ᶠ z, ((N.div hr').mult z : ℝ) * c z =
      ∑ᶠ z, ((N.div hr).mult z : ℝ) * c z + ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z := by
    simp_rw [hord]
    rw [← finsum_add_distrib (hfin _) (hfin _)]
    refine finsum_congr fun z => ?_
    rw [HermLB.div, HermLB.div, mult_eq_add_ord N.isLB hr hr' f hf z, hord]
    push_cast
    ring
  unfold recVal
  rw [hsum, mixArch_zero, mixArch_zero]
  rcases _root_.GlobalTheory.MixHt.amb_vertical_or_arithVar k Y q hA (0 + 1) hd with ⟨l, hl, ⟨alg⟩, hemp⟩ | ⟨e, he, hq⟩
  · have h0 : ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z = 0 :=
      @_root_.GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero k _ Y _ _ q hA hd l hl alg (f : Y.functionField) f.ne_zero
    rw [h0, archInt_eq_zero hemp, archInt_eq_zero hemp]
    ring
  · obtain rfl : e = 0 := by omega
    have := hq.finite_emb
    rw [GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r hr,
      GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r' hr',
      _root_.GlobalTheory.CurveProd.product_formula_curve k Y q hq (f : Y.functionField) f.ne_zero]
    have hlog (σ : k →+* ℂ) (y : CxPts q σ) : logNorm (N.φ σ) r' y =
        Real.log ‖ratVal (f : Y.functionField) y‖ + logNorm (N.φ σ) r y := by
      have hy := GlobalTheory.TwistTop.under_eq_genericPoint hq y
      have hreg (g : Y.functionField) : RegAt (under y) g := by
        rw [hy]; exact regAt_genericPoint g
      have hunit (g : Y.functionFieldˣ) : UnitAt (under y) (g : Y.functionField) := by
        rw [hy]; exact unitAt_genericPoint g.ne_zero
      have hi : genericPoint Y ∈ N.B.U (pick (N.φ σ).isLB y) :=
        gen_mem (mem_ptsIn.1 (mem_pick (N.φ σ).isLB y))
      simp only [logNorm]
      rw [hf _ hi, Units.val_mul, ratVal_mul (hreg _) (hreg _), norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit _)))
          (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit f)))]
      ring
    have hσ (σ : k →+* ℂ) : ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r' y =
        ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (f : Y.functionField) y‖ + ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r y := by
      have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
      simp_rw [hlog σ]
      exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
    simp_rw [hσ]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    ring

end GlobalTheory.CurveIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdEqChart

theorem boundary_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → ∀ (m : ℕ) (t : Fin m → R), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ k, t k} := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy hrad m t ht hab
  have key : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal := fun p =>
    ⟨fun h => (hab p).1 (_root_.GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range g n F S j R ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p h),
     fun h => _root_.GlobalTheory.AbChart.mem_range_of_mem_abLocus g n F S j R b ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p ((hab p).2 h)⟩
  refine ⟨key, GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span S j.opensRange R ξ _ (_root_.GlobalTheory.RelParamRad.isRadical_span_prod _ R b m t ht) (fun p => ?_) hrad⟩
  rw [Scheme.Hom.coe_opensRange]
  exact key p

end GlobalTheory.BdEqChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinear
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

theorem resG_secMap_lin {U V : Z.Opens} (h : V ≤ U) (r : R) :
    resG Z h ((secMap s U).hom r) = (secMap s V).hom r := by
  exact (Sec.res s h).commutes r

theorem resG_sub_sum_lin {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) {N : ℕ} (r : Fin N → R)
    (y : Fin N → Γ(Z, U)) :
    resG Z h (x - ∑ k, (secMap s U).hom (r k) * y k) =
      resG Z h x - ∑ k, (secMap s V).hom (r k) * resG Z h (y k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, resG_secMap_lin]

theorem isCocycle_sub_sum_lin {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {N : ℕ}
    (r : Fin N → R) {e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')} (he : ∀ k, IsCocycle W (e k)) :
    IsCocycle W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') := by
  intro i i' i''
  beta_reduce
  rw [resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]
  simp only [← hc i i' i'', ← he _ i i' i'', mul_add,
    Finset.sum_add_distrib]
  ring

theorem fc_sub_sum_lin (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {N : ℕ}
    (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')) :
    fc s W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') =
      fc s W c - ∑ k, r k • fc s W (e k) := by
  funext V V' a
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  exact resG_sub_sum_lin s _ _ r _

theorem cmp_sub_sum_lin : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  intro R _ Z s J W hW c hc N r e he
  rw [cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]
  congr 2
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  exact fc_sub_sum_lin s W c r e

end GlobalTheory.CechCmp
end
end

